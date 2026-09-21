'use strict';

/* ABX 盲听测试前端
 *
 * 播放引擎基于 Web Audio API：
 * - A / B 解码一次，X 按题解码并缓存
 * - 切换音源 / 切换题目时保持播放位置与暂停状态
 * - 统一时间轴 = min(A 时长, B 时长)
 * - 片段循环：入点 / 出点基于统一时间轴（区间 ≥ 0.5 秒），启用时用
 *   AudioBufferSourceNode 原生 loop 在出点处采样级跳回入点；切换音源 /
 *   换题 / 拖动进度后循环区间与播放 / 暂停状态保持，且不会越过较短音频
 * - 可选电平匹配：统一时间轴内汇总各声道样本计算 RMS，
 *   以较安静音源为基准仅衰减较响者（-24～0 dB），A / B / X 各经一个 GainNode
 * - A/B/X 切换使用可配置（5～100 ms，可关闭）等功率交叉淡化：新旧音源
 *   从同一时间位置并行播放，旧源 cos 曲线淡出、新源 sin 曲线淡入；连续
 *   快速切换时从当前实时增益平滑转向最后一次选择，过时节点与回调立即取消
 */

const $ = (sel) => document.querySelector(sel);

// ---------------------------------------------------------------------------
// 全局状态
// ---------------------------------------------------------------------------

let session = null;          // { id, numTrials, recoveryToken }
let answers = [];            // 每题 'A' | 'B' | null
let currentTrial = 0;

// ---------------------------------------------------------------------------
// 恢复标识（仅存本机浏览器 localStorage，不会离开本机）
// ---------------------------------------------------------------------------

const RECOVERY_KEY = 'abx.recovery';
let pendingResume = null;    // 页面加载时探测到的可恢复会话

function saveRecovery() {
  if (!session || !session.recoveryToken) return;
  localStorage.setItem(RECOVERY_KEY, JSON.stringify({
    token: session.recoveryToken,
    trial: currentTrial,
  }));
}

function loadSavedRecovery() {
  try {
    const saved = JSON.parse(localStorage.getItem(RECOVERY_KEY));
    if (saved && typeof saved.token === 'string') return saved;
  } catch (_) { /* 忽略损坏的本地数据 */ }
  return null;
}

function clearRecovery() {
  localStorage.removeItem(RECOVERY_KEY);
}

let actx = null;             // AudioContext
const buffers = { A: null, B: null, X: null };
const xCache = new Map();    // trialIndex -> { buf, rms }
let timeline = 0;            // 统一时间轴（较短时长，秒）

let currentSrc = 'A';        // 最后选择的音源 'A' | 'B' | 'X'（淡化中也立即指向目标）
let playing = false;
let startCtxTime = 0;        // 本次播放起点对应的 AudioContext 时间（进度锚点，淡化期间不动）
let startOffset = 0;         // 本次播放起点对应的音频位置（秒）

// 多声部播放：交叉淡化期间新旧音源从同一位置并行播放。
// voices: 音源键 -> { key, node, fg(淡化用 GainNode), useLoop }
// 路由：BufferSource -> fg(交叉淡化) -> gains[key](电平匹配) -> destination
const voices = new Map();
let primaryVoice = null;     // 负责播放到时间轴末尾自然结束的声部（最后选择的音源）
let fade = null;             // 进行中的交叉淡化 { t0, dur, start: {A,B,X}, target }
let fadeGen = 0;             // 代号：使上一次淡化排程的收尾回调作废
let fadeTimer = 0;

// 电平匹配：A / B / X 各经一个 GainNode，仅衰减较响音源
const gains = { A: null, B: null, X: null };
const rms = { A: NaN, B: NaN, X: NaN };   // 统一时间轴内、汇总各声道的 RMS
const gainDb = { A: 0, B: 0, X: 0 };      // 各音源调整量（dB，≤ 0）
let levelRef = null;         // 基准 RMS（较安静音源）；A/B RMS 无效时为 null
let levelMatchOn = false;    // 开关状态

// 片段循环：入点 / 出点（秒，基于统一时间轴；null = 未设置）
const MIN_LOOP = 0.5;        // 循环区间最短时长（秒）
let loopIn = null;
let loopOut = null;

// 交叉淡化：等功率（sin/cos），可配置 5～100 ms，0 = 关闭（即时硬切）
const FADE_MIN_MS = 5;
const FADE_MAX_MS = 100;
const FADE_STEPS = 16;       // AudioParam 线性斜坡分段数（分段足够密，听感等同平滑曲线）
let fadeMs = 20;

// ---------------------------------------------------------------------------
// 视图切换
// ---------------------------------------------------------------------------

function show(viewId) {
  document.querySelectorAll('.view').forEach((v) => v.classList.add('hidden'));
  $('#' + viewId).classList.remove('hidden');
}

// ---------------------------------------------------------------------------
// 播放引擎
// ---------------------------------------------------------------------------

function position() {
  if (!playing) return startOffset;
  const t = startOffset + actx.currentTime - startCtxTime;
  // 循环播放中：到达出点后从入点继续，显示位置在 [入点, 出点) 内回绕
  if (loopActive() && startOffset < loopOut && t >= loopOut) {
    return loopIn + ((t - loopIn) % (loopOut - loopIn));
  }
  return Math.min(t, timeline);
}

function play() {
  if (playing || !buffers[currentSrc]) return;
  if (startOffset >= timeline) startOffset = 0;
  const v = createVoice(currentSrc, startOffset, true);
  if (!v) return;
  startCtxTime = actx.currentTime;
  playing = true;
  updatePlayBtn();
}

/**
 * 创建并启动一个播放声部（不改动 playing / 进度锚点）。
 * 循环启用且起点在出点之前：用原生 loop，到达出点（loopEnd）即采样级
 * 精确跳回入点（loopStart）；否则只在统一时间轴剩余时长内播放。
 * 返回声部对象；起点已在时间轴之外（剩余时长 ≤ 0）时返回 null。
 */
function createVoice(key, offset, isPrimary) {
  const buf = buffers[key];
  if (!buf) return null;
  const useLoop = loopActive() && offset < loopOut;
  const remain = Math.max(0, Math.min(timeline, buf.duration) - offset);
  if (!useLoop && remain <= 0) return null;

  const node = actx.createBufferSource();
  node.buffer = buf;
  const fg = actx.createGain();
  // 主声部独占播放：满幅起步；淡化中的新声部从 0 起步，由淡化曲线抬升
  fg.gain.value = isPrimary ? 1 : 0;
  node.connect(fg).connect(gains[key]); // fg：交叉淡化；gains[key]：电平匹配
  if (useLoop) {
    node.loop = true;
    node.loopStart = loopIn;
    node.loopEnd = loopOut;
    node.start(0, offset);
  } else {
    node.start(0, offset, remain);
  }

  const v = { key, node, fg, useLoop };
  voices.set(key, v);
  if (isPrimary) {
    primaryVoice = v;
    // 只有最后选择的音源自然播到时间轴末尾才结束播放状态
    node.onended = () => {
      if (primaryVoice !== v) return;   // 已被后选声部取代
      endTransport();
    };
  }
  return v;
}

/** 主声部自然播放到时间轴末尾：收束到停止态（位置回到 0，与原有语义一致） */
function endTransport() {
  teardownVoices();
  playing = false;
  startOffset = 0;
  updatePlayBtn();
  updateTransport();
}

/**
 * 收束并拆除全部声部：淡化增益立即归零，停止 / 断开节点，清空声部表。
 * 进行中淡化的排程与回调一律作废，避免过时节点继续发声或叠加。
 * 暂停 / 拖动 / 换题 / 循环变更后再由调用方以当前音源重新建立单一声部。
 */
function teardownVoices() {
  cancelFade();
  const now = actx ? actx.currentTime : 0;
  for (const v of voices.values()) {
    holdGain(v.fg.gain, 0, now);
    v.node.onended = null;
    try { v.node.stop(now); } catch (_) { /* 已停止 */ }
    try { v.node.disconnect(); } catch (_) { /* 已断开 */ }
  }
  voices.clear();
  primaryVoice = null;
}

/** 取消进行中的淡化（保留声部与当前实时增益），并使待执行回调作废 */
function cancelFade() {
  if (fadeTimer) { clearTimeout(fadeTimer); fadeTimer = 0; }
  fade = null;
  fadeGen++;
}

function pause() {
  if (!playing) return;
  const pos = position();
  teardownVoices(); // 暂停即收束：淡化声部全部停止，状态确定
  playing = false;
  startOffset = pos;
  updatePlayBtn();
}

/**
 * 切换 A / B / X，保持播放位置与暂停状态。
 * 播放中且淡化开启：新旧音源从同一时间位置并行播放，做等功率交叉淡化；
 * 连续快速点击时以当前实时增益为新起点，重新排程到最后一次选择，
 * 上一次淡化的节点收尾与回调立即作废，音量始终等功率、不叠加。
 */
function switchSource(which) {
  if (which === currentSrc || !buffers[which]) return;
  currentSrc = which;
  updateSrcButtons();
  if (!playing) {
    // 暂停态切换：只换音源标记，下次播放从新音源当前位置开始（保持原语义）
    teardownVoices();
    return;
  }
  if (fadeMs <= 0) {
    // 关闭淡化：原位置即时硬切
    const pos = position();
    teardownVoices();
    startOffset = pos;
    startCtxTime = actx.currentTime;
    const v = createVoice(which, pos, true);
    if (!v) endTransport();
    return;
  }
  startCrossfade(which);
}

/**
 * 从当前实时增益出发，等功率交叉淡化到目标音源。
 * 等功率：目标沿 sin 曲线 0→1、其余沿各自曲线 →0，且每一刻各声部
 * 增益平方和恒为 1，总响度不变。所有现有声部与新声部共用同一进度锚点
 * （同一 startCtxTime / startOffset），从同一时间位置并行播放，无进度漂移。
 */
function startCrossfade(targetKey) {
  const now = actx.currentTime;
  const dur = fadeMs / 1000;

  // 目标声部不存在则在当前位置补建（与在播声部同一锚点）
  if (!voices.has(targetKey)) {
    const v = createVoice(targetKey, position(), false);
    if (!v) return; // 已到时间轴末尾（理论上在播时不会发生）
  }

  const myGen = ++fadeGen;              // 使上一次淡化的收尾回调作废
  if (fadeTimer) clearTimeout(fadeTimer);

  const t0 = now;
  const startGain = {};                 // 淡化起点的实时增益快照
  for (const k of voices.keys()) startGain[k] = clamp01(voices.get(k).fg.gain.value);
  fade = { t0, dur, start: startGain, target: targetKey };

  // 等功率分配（平方和恒为 1，且每个声部各自单调）：
  // - 目标声部：sin(θ)，θ 从 asin(起点目标增益) 转到 π/2（g₀→1，单调上升）
  // - 全部淡出声部共享 cos(θ) 包络（单调降到 0），按起点增益平方占比恒定分配。
  //   由于起点快照满足 Σg²=1，淡出起点合计恰为 cos(θ 起点)，故全程平方和为 1。
  const keys = [...voices.keys()];
  const gT0 = startGain[targetKey] || 0;
  const a0 = Math.asin(gT0);
  let stalePower = 0;
  for (const k of keys) if (k !== targetKey) stalePower += startGain[k] ** 2;
  const staleBase = Math.sqrt(stalePower);   // = cos(a0)（快照等功率时）
  const share = {};
  for (const k of keys) {
    share[k] = k === targetKey
      ? 1
      : (staleBase > 1e-9 ? startGain[k] / staleBase : 0);
  }

  const curves = {};
  for (const k of keys) curves[k] = new Array(FADE_STEPS + 1);
  for (let i = 0; i <= FADE_STEPS; i++) {
    const u = i / FADE_STEPS;
    const theta = a0 + (Math.PI / 2 - a0) * u;
    const env = Math.cos(theta);
    for (const k of keys) {
      curves[k][i] = k === targetKey ? Math.sin(theta) : share[k] * env;
    }
  }

  for (const k of keys) {
    const param = voices.get(k).fg.gain;
    // 作废旧自动化并在 t0 建立明确起点事件，再以多段线性斜坡走完等功率曲线
    try {
      if (typeof param.cancelAndHoldAtTime === 'function') {
        param.cancelAndHoldAtTime(t0);
      } else {
        param.cancelScheduledValues(t0);
      }
    } catch (_) { /* 无待排事件 */ }
    param.setValueAtTime(curves[k][0], t0 + 1e-6);
    for (let i = 1; i <= FADE_STEPS; i++) {
      param.linearRampToValueAtTime(curves[k][i], t0 + (dur * i) / FADE_STEPS);
    }
  }

  // 淡化结束：目标增益钉为 1，过时声部停止并断开（等功率已精确收敛）
  fadeTimer = setTimeout(() => {
    fadeTimer = 0;
    if (myGen !== fadeGen) return;      // 已被新的切换 / 收束取代
    fade = null;
    const target = voices.get(targetKey);
    for (const [k, v] of voices) {
      if (k === targetKey) continue;
      v.node.onended = null;
      try { v.node.stop(); } catch (_) { /* 已停止 */ }
      try { v.node.disconnect(); } catch (_) { /* 已断开 */ }
      voices.delete(k);
    }
    if (target) {
      // 淡化曲线终点已为 1，这里取消残留自动化并钉死为满幅（避免任何再插值）
      try { target.fg.gain.cancelScheduledValues(actx.currentTime); } catch (_) { /* 无 */ }
      target.fg.gain.value = 1;
      primaryVoice = target;
    } else {
      endTransport(); // 目标声部已不在（极端时序）：一致收束到停止态
    }
  }, fadeMs + 30);
}

const clamp01 = (x) => Math.max(0, Math.min(1, x));

/**
 * 在 time 时刻把 AudioParam 固定为指定值并作废其后续自动化（无爆音）。
 * 优先 cancelAndHoldAtTime（保持到该时刻的连续值），再补一个定值事件；
 * 不支持时退化为「取消后续排程 + 立即定值」。
 */
function holdGain(param, value, time) {
  try {
    if (typeof param.cancelAndHoldAtTime === 'function') {
      param.cancelAndHoldAtTime(time);
      param.setValueAtTime(value, time + 1e-6);
      return;
    }
  } catch (_) { /* 退化处理见下 */ }
  try { param.cancelScheduledValues(time); } catch (_) { /* 无待排事件 */ }
  param.setTargetAtTime(value, time, 0.001);
  try { param.setValueAtTime(value, time + 0.004); } catch (_) { /* 忽略 */ }
}

/** 拖动进度：收束淡化并在新位置以当前音源重建（保持播放 / 暂停状态） */
function seekTo(t) {
  const wasPlaying = playing;
  const pos = Math.max(0, Math.min(t, timeline));
  if (wasPlaying) teardownVoices();
  playing = false;
  startOffset = pos;
  if (wasPlaying) {
    const v = createVoice(currentSrc, pos, true);
    if (v) {
      startCtxTime = actx.currentTime;
      playing = true;
    }
  }
  updateTransport();
}

// ---------------------------------------------------------------------------
// 片段循环：在统一时间轴上设置入点 / 出点，播放到出点即从入点继续
// ---------------------------------------------------------------------------

/** 循环是否生效（入 / 出点均已设置且区间 ≥ 0.5 秒） */
function loopActive() {
  return loopIn !== null && loopOut !== null && loopOut - loopIn >= MIN_LOOP;
}

/** 归一化入 / 出点：限制在 [0, timeline] 内，且区间至少 0.5 秒（必要时回移入点） */
function normalizeLoop() {
  if (loopIn !== null) loopIn = Math.max(0, Math.min(loopIn, timeline));
  if (loopOut !== null) loopOut = Math.max(0, Math.min(loopOut, timeline));
  if (loopIn !== null && loopOut !== null && loopOut - loopIn < MIN_LOOP) {
    loopOut = Math.min(timeline, loopIn + MIN_LOOP);
    loopIn = Math.max(0, loopOut - MIN_LOOP);
  }
}

/**
 * 循环区间变更后无缝重建播放（保持播放 / 暂停状态）：
 * 当前位置已越过新出点时立即跳回入点；循环未参与播放时不打断当前声音。
 * 进行中的交叉淡化在此一致收束：只保留当前音源从新配置重建。
 */
function restartForLoop(pos, wasActive) {
  const snap = loopActive() && pos >= loopOut;
  if (playing) {
    if (!wasActive && !loopActive()) return;
    teardownVoices();
    playing = false;
    startOffset = snap ? loopIn : pos;
    play();
  } else if (snap) {
    startOffset = loopIn;
    updateTransport();
  }
}

/** 渲染循环状态：按钮高亮、状态行、时间轴上的范围高亮与入 / 出点刻度 */
function renderLoop() {
  const inSet = loopIn !== null;
  const outSet = loopOut !== null;
  const active = loopActive();

  $('#btnLoopIn').classList.toggle('set', inSet);
  $('#btnLoopOut').classList.toggle('set', outSet);
  $('#btnLoopClear').disabled = !inSet && !outSet;

  const info = $('#loopInfo');
  if (timeline > 0 && timeline < MIN_LOOP) {
    info.textContent = '音频不足 0.5 秒，无法设置循环';
  } else if (active) {
    info.textContent =
      `循环已启用：${fmt(loopIn)} → ${fmt(loopOut)}（${(loopOut - loopIn).toFixed(1)} 秒）`;
  } else if (inSet && outSet) {
    info.textContent = '循环区间过短（至少 0.5 秒）';
  } else if (inSet) {
    info.textContent = `入点 ${fmt(loopIn)} · 待设置出点`;
  } else if (outSet) {
    info.textContent = `出点 ${fmt(loopOut)} · 待设置入点`;
  } else {
    info.textContent = '循环未设置';
  }
  info.classList.toggle('on', active);

  // 时间轴下方的循环范围高亮与入 / 出点刻度
  const region = $('#loopRegion');
  const showRegion = active && timeline > 0;
  region.classList.toggle('show', showRegion);
  if (showRegion) {
    region.style.left = `${(loopIn / timeline) * 100}%`;
    region.style.width = `${((loopOut - loopIn) / timeline) * 100}%`;
  }
  const edgeIn = $('#loopEdgeIn');
  const edgeOut = $('#loopEdgeOut');
  edgeIn.classList.toggle('show', inSet && timeline > 0);
  edgeOut.classList.toggle('show', outSet && timeline > 0);
  if (inSet && timeline > 0) edgeIn.style.left = `${(loopIn / timeline) * 100}%`;
  if (outSet && timeline > 0) edgeOut.style.left = `${(loopOut / timeline) * 100}%`;
}

// ---------------------------------------------------------------------------
// 电平匹配（可选）：消除 A/B 响度差造成的盲测线索
// ---------------------------------------------------------------------------

const RMS_MIN = 1e-6;        // RMS 下限，低于此值视为无声
const GAIN_MIN_DB = -24;     // 衰减下限（dB）

/** 统一时间轴内、汇总各声道样本的 RMS */
function computeRms(buf, seconds) {
  const len = Math.min(buf.length, Math.floor(seconds * buf.sampleRate));
  if (len <= 0) return NaN;
  let sum = 0;
  for (let ch = 0; ch < buf.numberOfChannels; ch++) {
    const data = buf.getChannelData(ch);
    for (let i = 0; i < len; i++) sum += data[i] * data[i];
  }
  return Math.sqrt(sum / (len * buf.numberOfChannels));
}

const validRms = (r) => Number.isFinite(r) && r >= RMS_MIN;

/** 由 RMS 重算各音源调整量（dB）：以较安静音源为基准，仅衰减较响者 */
function refreshLevelMatch() {
  // A 或 B 的 RMS 无效（< 1e-6 或非有限值）时不做匹配，全部保持 0 dB
  levelRef = validRms(rms.A) && validRms(rms.B) ? Math.min(rms.A, rms.B) : null;
  for (const k of ['A', 'B', 'X']) {
    let db = 0;
    if (levelRef !== null && validRms(rms[k])) {
      db = 20 * Math.log10(levelRef / rms[k]);
      db = Math.max(GAIN_MIN_DB, Math.min(0, db)); // 衰减限制在 -24～0 dB
    }
    gainDb[k] = db;
  }
  applyGains();
  renderLevelInfo();
}

/** 按开关状态把调整量写入 GainNode；不打断播放，关闭立即恢复原始电平 */
function applyGains() {
  if (!actx) return;
  for (const k of ['A', 'B', 'X']) {
    if (gains[k]) {
      gains[k].gain.value = Math.pow(10, (levelMatchOn ? gainDb[k] : 0) / 20);
    }
  }
}

function renderLevelInfo() {
  const fmtDb = (db) => {
    const s = db.toFixed(1);
    return s === '-0.0' ? '0.0' : s;
  };
  const el = $('#levelInfo');
  el.textContent = `A ${fmtDb(gainDb.A)} dB · B ${fmtDb(gainDb.B)} dB`;
  el.classList.toggle('off', !levelMatchOn);
}

// ---------------------------------------------------------------------------
// 音频加载
// ---------------------------------------------------------------------------

async function fetchBuffer(url) {
  const res = await fetch(url);
  if (!res.ok) throw new Error('音频加载失败');
  const raw = await res.arrayBuffer();
  return actx.decodeAudioData(raw);
}

async function loadTrial(n) {
  currentTrial = n;
  saveRecovery(); // 记住当前题号，刷新后可回到本题
  if (!xCache.has(n)) {
    const buf = await fetchBuffer(`/api/session/${session.id}/trial/${n}/x`);
    // 每题 X 与 A/B 按同一规则计算 RMS（统一时间轴内、汇总各声道）
    xCache.set(n, { buf, rms: computeRms(buf, timeline) });
  }
  const cached = xCache.get(n);
  buffers.X = cached.buf;
  rms.X = cached.rms;
  refreshLevelMatch(); // X 的调整量随题更新
  // 若当前正在听 X，把在播声部换成本题的 X（保持位置与播放状态）。
  // 交叉淡化中则先收束到 X（取消过时声部与回调），再换缓冲重建，
  // 避免旧题 X 声部与新题 X 声部叠加发声。
  if (currentSrc === 'X' && playing) {
    const pos = position();
    teardownVoices();
    playing = false;
    startOffset = pos;
    const v = createVoice('X', pos, true);
    if (v) {
      startCtxTime = actx.currentTime;
      playing = true;
    }
  } else {
    // 暂停 / 当前听 A·B：淡化里可能残留正在淡出的 X，直接停掉它再换缓冲
    teardownVoices();
  }
  renderTrial();
}

// ---------------------------------------------------------------------------
// UI 渲染
// ---------------------------------------------------------------------------

function fmt(t) {
  const m = Math.floor(t / 60);
  const s = t - m * 60;
  return `${m}:${s.toFixed(1).padStart(4, '0')}`;
}

function updatePlayBtn() {
  $('#btnPlay').textContent = playing ? '⏸ 暂停' : '▶ 播放';
}

function updateTransport() {
  $('#seek').value = position();
  $('#timeLabel').textContent = `${fmt(position())} / ${fmt(timeline)}`;
}

function updateSrcButtons() {
  document.querySelectorAll('.src-btn').forEach((b) => {
    b.classList.toggle('active', b.dataset.src === currentSrc);
  });
}

function renderTrial() {
  $('#trialLabel').textContent = `第 ${currentTrial + 1} / ${session.numTrials} 题`;
  $('#btnPrev').disabled = currentTrial === 0;
  $('#btnNext').disabled = currentTrial === session.numTrials - 1;

  const ans = answers[currentTrial];
  $('#btnAnsA').classList.toggle('selected', ans === 'A');
  $('#btnAnsB').classList.toggle('selected', ans === 'B');

  // 进度圆点
  const progress = $('#progress');
  progress.innerHTML = '';
  for (let i = 0; i < session.numTrials; i++) {
    const dot = document.createElement('button');
    dot.className = 'dot';
    if (answers[i]) dot.classList.add('done');
    if (i === currentTrial) dot.classList.add('current');
    dot.textContent = i + 1;
    dot.addEventListener('click', () => loadTrial(i));
    progress.appendChild(dot);
  }

  const allAnswered = answers.every(Boolean);
  $('#btnSubmit').disabled = !allAnswered;
  $('#btnSubmit').textContent = allAnswered
    ? '提交并揭晓答案'
    : `提交并揭晓答案（还剩 ${answers.filter((a) => !a).length} 题未答）`;
}

function tick() {
  if (playing) updateTransport();
  requestAnimationFrame(tick);
}

// ---------------------------------------------------------------------------
// 事件绑定
// ---------------------------------------------------------------------------

/** 进入测试视图：解码 A/B、初始化播放状态并加载当前题（新建与恢复共用） */
async function enterTest() {
  // AudioContext 需在用户手势中创建
  actx = actx || new (window.AudioContext || window.webkitAudioContext)();
  await actx.resume();

  // 每个音源一个 GainNode（电平匹配用），只创建一次
  if (!gains.A) {
    for (const k of ['A', 'B', 'X']) {
      gains[k] = actx.createGain();
      gains[k].connect(actx.destination);
    }
  }

  // 新测试 / 恢复：播放引擎彻底复位（也清掉上一轮可能残留的淡化声部）
  teardownVoices();
  fadeMs = readFadeMs();
  renderFadeInfo();

  buffers.A = await fetchBuffer(`/api/session/${session.id}/audio/A`);
  buffers.B = await fetchBuffer(`/api/session/${session.id}/audio/B`);
  // 统一时间轴：以较短时长为准
  timeline = Math.min(buffers.A.duration, buffers.B.duration);
  $('#seek').max = timeline;

  // 片段循环：新会话清空；音频短于 0.5 秒时禁用循环按钮
  loopIn = null;
  loopOut = null;
  const canLoop = timeline >= MIN_LOOP;
  $('#btnLoopIn').disabled = !canLoop;
  $('#btnLoopOut').disabled = !canLoop;
  renderLoop();

  // 电平匹配：解码后在统一时间轴内汇总各声道样本计算 RMS
  rms.A = computeRms(buffers.A, timeline);
  rms.B = computeRms(buffers.B, timeline);
  rms.X = NaN; // 待 loadTrial 解码本题 X 后计算
  levelMatchOn = $('#chkLevelMatch').checked;
  refreshLevelMatch();

  currentSrc = 'A';
  playing = false;
  startOffset = 0;
  updateSrcButtons();
  updatePlayBtn();
  updateTransport();

  await loadTrial(currentTrial);
  show('view-test');
}

$('#btnStart').addEventListener('click', async () => {
  const errEl = $('#uploadError');
  errEl.textContent = '';
  const fa = $('#fileA').files[0];
  const fb = $('#fileB').files[0];
  if (!fa || !fb) {
    errEl.textContent = '请同时选择音频 A 和音频 B';
    return;
  }

  const btn = $('#btnStart');
  btn.disabled = true;
  btn.textContent = '上传并解码中…';
  try {
    // 开始新测试即放弃旧的待恢复会话（主动删除，恢复标识随之失效）
    if (pendingResume) {
      await fetch(`/api/session/${pendingResume.id}`, { method: 'DELETE' }).catch(() => {});
      pendingResume = null;
      $('#view-resume').classList.add('hidden');
    }

    const fd = new FormData();
    fd.append('a', fa);
    fd.append('b', fb);
    fd.append('numTrials', $('#numTrials').value);
    const res = await fetch('/api/session', { method: 'POST', body: fd });
    const data = await res.json();
    if (!res.ok) throw new Error(data.error || '创建会话失败');

    session = data;
    answers = Array(data.numTrials).fill(null);
    currentTrial = 0;
    xCache.clear();
    saveRecovery(); // 保存恢复标识，刷新/重开页面可找回本会话

    await enterTest();
  } catch (e) {
    errEl.textContent = e.message;
  } finally {
    btn.disabled = false;
    btn.textContent = '开始测试';
  }
});

// ---------------------------------------------------------------------------
// 会话恢复（刷新 / 重新打开页面后找回未提交的测试）
// ---------------------------------------------------------------------------

async function initRecovery() {
  const saved = loadSavedRecovery();
  if (!saved) return;
  try {
    const res = await fetch('/api/session/recover', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ token: saved.token }),
    });
    if (!res.ok) throw new Error('recover failed');
    const data = await res.json();
    pendingResume = {
      ...data,
      token: saved.token,
      trial: Math.min(Math.max(0, saved.trial | 0), data.numTrials - 1),
    };
    const answered = data.answers.filter(Boolean).length;
    $('#resumeInfo').textContent =
      `检测到本机有未提交的测试：共 ${data.numTrials} 题，已答 ${answered} 题，` +
      `上次进行到第 ${pendingResume.trial + 1} 题。`;
    $('#view-resume').classList.remove('hidden');
  } catch (_) {
    clearRecovery(); // 会话已提交、删除或过期，恢复标识不再有效
  }
}

$('#btnResume').addEventListener('click', async () => {
  if (!pendingResume) return;
  const btn = $('#btnResume');
  btn.disabled = true;
  btn.textContent = '正在恢复…';
  const resume = pendingResume;
  try {
    session = {
      id: resume.id,
      numTrials: resume.numTrials,
      recoveryToken: resume.token,
    };
    answers = resume.answers.slice();
    currentTrial = resume.trial;
    xCache.clear();
    await enterTest();
    pendingResume = null;
    $('#view-resume').classList.add('hidden');
  } catch (e) {
    alert(e.message || '恢复失败');
    btn.disabled = false;
    btn.textContent = '继续上次测试';
  }
});

$('#btnDiscardResume').addEventListener('click', async () => {
  if (pendingResume) {
    await fetch(`/api/session/${pendingResume.id}`, { method: 'DELETE' }).catch(() => {});
  }
  pendingResume = null;
  clearRecovery();
  $('#view-resume').classList.add('hidden');
});

$('#btnPlay').addEventListener('click', async () => {
  await actx.resume();
  if (playing) pause();
  else play();
});

document.querySelectorAll('.src-btn').forEach((b) => {
  b.addEventListener('click', () => switchSource(b.dataset.src));
});

$('#seek').addEventListener('input', (e) => seekTo(parseFloat(e.target.value)));

// 片段循环：以当前播放位置设置入点 / 出点（先后次序不限），一键清除。
// 循环区间是全局状态：切换 A / B / X、换题、拖动进度都不会改变它
$('#btnLoopIn').addEventListener('click', () => {
  if (timeline < MIN_LOOP) return;
  const wasActive = loopActive();
  const pos = position();
  loopIn = pos;
  normalizeLoop();
  restartForLoop(pos, wasActive);
  renderLoop();
});

$('#btnLoopOut').addEventListener('click', () => {
  if (timeline < MIN_LOOP) return;
  const wasActive = loopActive();
  const pos = position();
  loopOut = pos;
  normalizeLoop();
  restartForLoop(pos, wasActive);
  renderLoop();
});

$('#btnLoopClear').addEventListener('click', () => {
  const wasActive = loopActive();
  const pos = position(); // 先取当前实际位置（旧循环配置下的回绕位置）
  loopIn = loopOut = null;
  if (playing && wasActive) {
    teardownVoices();
    playing = false;
    startOffset = pos;
    play();
  }
  renderLoop();
});

// 电平匹配开关：只改 GainNode 增益，播放位置与播放/暂停状态不受影响
$('#chkLevelMatch').addEventListener('change', (e) => {
  levelMatchOn = e.target.checked;
  applyGains(); // 关闭后立即恢复原始电平
  renderLevelInfo();
});

// ---------------------------------------------------------------------------
// 交叉淡化设置：等功率、5～100 ms，可关闭
// ---------------------------------------------------------------------------

/** 读取界面淡化设置：勾选时取 5～100 ms，未勾选为 0（即时硬切） */
function readFadeMs() {
  if (!$('#chkCrossfade').checked) return 0;
  const n = parseInt($('#fadeMs').value, 10);
  if (!Number.isFinite(n)) return fadeMs;
  return Math.max(FADE_MIN_MS, Math.min(FADE_MAX_MS, n));
}

function renderFadeInfo() {
  $('#fadeMs').disabled = !$('#chkCrossfade').checked;
  $('#fadeMsVal').textContent = $('#chkCrossfade').checked
    ? `${fadeMs} ms`
    : '已关闭';
}

$('#chkCrossfade').addEventListener('change', () => {
  fadeMs = readFadeMs();
  // 关闭时若正在淡化，立即收束到最后选择的音源，避免遗留淡出声部
  if (fadeMs === 0 && playing) {
    const pos = position();
    teardownVoices();
    playing = false;
    startOffset = pos;
    const v = createVoice(currentSrc, pos, true);
    if (v) {
      startCtxTime = actx.currentTime;
      playing = true;
    }
  }
  renderFadeInfo();
});

$('#fadeMs').addEventListener('input', (e) => {
  const n = parseInt(e.target.value, 10);
  if (!Number.isFinite(n)) return;
  fadeMs = Math.max(FADE_MIN_MS, Math.min(FADE_MAX_MS, n));
  e.target.value = fadeMs;
  // 仅影响之后的切换；淡化进行中不打断，保证当前过渡平滑完成
  renderFadeInfo();
});

$('#btnPrev').addEventListener('click', () => { if (currentTrial > 0) loadTrial(currentTrial - 1); });
$('#btnNext').addEventListener('click', () => { if (currentTrial < session.numTrials - 1) loadTrial(currentTrial + 1); });

async function sendAnswer(val) {
  answers[currentTrial] = val;
  renderTrial();
  const res = await fetch(`/api/session/${session.id}/answer`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ trial: currentTrial, answer: val }),
  });
  if (!res.ok) {
    const data = await res.json().catch(() => ({}));
    alert(data.error || '答案保存失败');
  }
}

$('#btnAnsA').addEventListener('click', () => sendAnswer('A'));
$('#btnAnsB').addEventListener('click', () => sendAnswer('B'));

$('#btnSubmit').addEventListener('click', async () => {
  if (!confirm('提交后将一次性揭晓全部答案，且不可再修改。确定提交？')) return;
  const res = await fetch(`/api/session/${session.id}/submit`, { method: 'POST' });
  const data = await res.json();
  if (!res.ok) {
    alert(data.error || '提交失败');
    return;
  }
  pause();
  clearRecovery(); // 提交后恢复标识立即失效（服务端同步作废）
  showResults(data.results);
});

$('#btnAgain').addEventListener('click', async () => {
  pause();
  teardownVoices();
  if (session) {
    await fetch(`/api/session/${session.id}`, { method: 'DELETE' }).catch(() => {});
  }
  session = null;
  answers = [];
  xCache.clear();
  clearRecovery();
  buffers.A = buffers.B = buffers.X = null;
  rms.A = rms.B = rms.X = NaN;
  refreshLevelMatch(); // 清空调整量显示，增益归零
  currentSrc = 'A';
  startOffset = 0;
  loopIn = null;
  loopOut = null;
  $('#fileA').value = '';
  $('#fileB').value = '';
  show('view-upload');
});

// ---------------------------------------------------------------------------
// 结果展示
// ---------------------------------------------------------------------------

function showResults(results) {
  const pct = (results.accuracy * 100).toFixed(1);
  $('#scoreLabel').textContent =
    `答对 ${results.correct} / ${results.total} 题，正确率 ${pct}%`;

  const tbody = $('#resultTable tbody');
  tbody.innerHTML = '';
  for (const d of results.detail) {
    const tr = document.createElement('tr');
    tr.className = d.correct ? 'right' : 'wrong';
    tr.innerHTML =
      `<td>${d.trial}</td><td>${d.x}</td><td>${d.answer}</td>` +
      `<td>${d.correct ? '✓ 正确' : '✗ 错误'}</td>`;
    tbody.appendChild(tr);
  }
  show('view-result');
}

// 启动 UI 刷新循环，并探测本机是否有可恢复的未提交会话
tick();
initRecovery();
