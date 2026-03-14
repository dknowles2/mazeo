'use strict';

const GRID_SIZE = 5;
const GRID_CELLS = GRID_SIZE * GRID_SIZE; // 25

// Walls between adjacent tiles (1-indexed, top-to-bottom left-to-right)
const WALLS = [
  [1,2],[3,4],[7,8],[9,10],[13,14],[16,17],[22,23],   // horizontal
  [1,6],[6,11],[7,12],[13,18],[19,24],[20,25],          // vertical
];

// Virtual grid positions for start/end boxes (row, col in extended grid space)
// Start-box sits one row above col 2; end-box sits one col right of row 2.
const START_POS = [-1, 2];
const END_POS   = [2, 5];

// Pre-compute blocked orthogonal edges from WALLS
const BLOCKED_EDGES = new Set();
for (const [t1, t2] of WALLS) {
  const r1 = Math.floor((t1 - 1) / GRID_SIZE), c1 = (t1 - 1) % GRID_SIZE;
  const r2 = Math.floor((t2 - 1) / GRID_SIZE), c2 = (t2 - 1) % GRID_SIZE;
  BLOCKED_EDGES.add(`${r1},${c1}|${r2},${c2}`);
  BLOCKED_EDGES.add(`${r2},${c2}|${r1},${c1}`);
}

// Distinct, accessible color pairs
const PALETTE = [
  { bg: '#dbeafe', fg: '#1e40af' },
  { bg: '#dcfce7', fg: '#166534' },
  { bg: '#fef9c3', fg: '#854d0e' },
  { bg: '#fce7f3', fg: '#9d174d' },
  { bg: '#ede9fe', fg: '#6b21a8' },
  { bg: '#ffedd5', fg: '#9a3412' },
  { bg: '#ccfbf1', fg: '#134e4a' },
  { bg: '#fee2e2', fg: '#991b1b' },
  { bg: '#fdf4ff', fg: '#701a75' },
  { bg: '#e0f2fe', fg: '#0c4a6e' },
];

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

// ── Solver ─────────────────────────────────────────────────────────────────────

/**
 * For each letter, compute the maximum number of times it appears in any
 * single word. This is the minimum number of cells of that letter the grid
 * must contain so every word can be satisfied.
 */
function computeRequired(words) {
  const required = {};
  for (const word of words) {
    const counts = {};
    for (const ch of word) counts[ch] = (counts[ch] || 0) + 1;
    for (const [ch, cnt] of Object.entries(counts)) {
      required[ch] = Math.max(required[ch] || 0, cnt);
    }
  }
  return required;
}

/**
 * Build and shuffle a flat array of 25 letters: required letters + random filler.
 */
function buildCells(required) {
  const ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const cells = [];
  for (const [ch, cnt] of Object.entries(required))
    for (let i = 0; i < cnt; i++) cells.push(ch);
  while (cells.length < GRID_CELLS)
    cells.push(ALPHA[Math.floor(Math.random() * 26)]);
  return shuffle(cells);
}

/** 2D cross product of vectors OA and OB (points as [row, col]). */
function cross2d(o, a, b) {
  return (a[1] - o[1]) * (b[0] - o[0]) - (a[0] - o[0]) * (b[1] - o[1]);
}

/**
 * True if point p lies on segment a–b.
 * Caller must ensure p is collinear with a and b before calling.
 */
function onSegment(p, a, b) {
  return Math.min(a[0], b[0]) <= p[0] && p[0] <= Math.max(a[0], b[0]) &&
         Math.min(a[1], b[1]) <= p[1] && p[1] <= Math.max(a[1], b[1]);
}

/**
 * Returns true if segment p1–p2 intersects segment p3–p4, including
 * degenerate cases where an endpoint lies exactly on the other segment
 * (T-intersections, collinear overlaps).
 */
function segmentsIntersect(p1, p2, p3, p4) {
  const d1 = cross2d(p3, p4, p1), d2 = cross2d(p3, p4, p2);
  const d3 = cross2d(p1, p2, p3), d4 = cross2d(p1, p2, p4);
  // Proper crossing
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
      ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0))) return true;
  // Degenerate: an endpoint lies exactly on the other segment
  if (d1 === 0 && onSegment(p1, p3, p4)) return true;
  if (d2 === 0 && onSegment(p2, p3, p4)) return true;
  if (d3 === 0 && onSegment(p3, p1, p2)) return true;
  if (d4 === 0 && onSegment(p4, p1, p2)) return true;
  return false;
}

/**
 * Returns the t parameter (0–1) along segment (ax,ay)→(bx,by) where it is
 * crossed by segment (cx,cy)→(dx,dy), or null if they don't cross at interior points.
 */
function segIntersectT(ax, ay, bx, by, cx, cy, dx, dy) {
  const rx = bx - ax, ry = by - ay;
  const sx = dx - cx, sy = dy - cy;
  const denom = rx * sy - ry * sx;
  if (Math.abs(denom) < 1e-6) return null;
  const t = ((cx - ax) * sy - (cy - ay) * sx) / denom;
  const u = ((cx - ax) * ry - (cy - ay) * rx) / denom;
  if (t <= 0.01 || t >= 0.99 || u <= 0.01 || u >= 0.99) return null;
  return t;
}

/**
 * Assign cells to each letter of `word` via backtracking.
 * Candidates are tried farthest-first (for spread), but any candidate whose
 * incoming segment would cross an earlier segment of the same word is skipped.
 * Returns the positions array, or null if no valid assignment exists.
 */
function findNonCrossingPath(word, letterCells) {
  const used = new Set();
  const pos  = [];

  function wouldCross(candidate) {
    if (pos.length < 2) return false;
    const prev = pos[pos.length - 1];
    for (let i = 0; i < pos.length - 2; i++) {
      if (segmentsIntersect(prev, candidate, pos[i], pos[i + 1])) return true;
    }
    // Check if candidate lies on the adjacent segment (pos[last-1] → prev),
    // which is excluded from the loop above but produces T-intersections
    const penult = pos[pos.length - 2];
    if (cross2d(penult, prev, candidate) === 0 && onSegment(candidate, penult, prev))
      return true;
    return false;
  }

  function bt(idx) {
    if (idx === word.length) return true;
    const ch = word[idx];

    const candidates = (letterCells[ch] || [])
      .filter(p => !used.has(`${p[0]},${p[1]}`));
    if (candidates.length === 0) return false;

    // Shuffle for variety, then sort farthest-first from the previous letter
    shuffle(candidates);
    if (pos.length > 0) {
      const [pr, pc] = pos[pos.length - 1];
      candidates.sort((a, b) =>
        (b[0]-pr)**2 + (b[1]-pc)**2 - (a[0]-pr)**2 - (a[1]-pc)**2
      );
    }

    for (const p of candidates) {
      if (wouldCross(p)) continue;
      used.add(`${p[0]},${p[1]}`);
      pos.push(p);
      if (bt(idx + 1)) return true;
      pos.pop();
      used.delete(`${p[0]},${p[1]}`);
    }
    return false;
  }

  if (!bt(0)) return null;

  // Final validation: confirm no two non-adjacent segments in the placed path cross.
  for (let i = 0; i < pos.length - 1; i++) {
    for (let j = i + 2; j < pos.length - 1; j++) {
      if (segmentsIntersect(pos[i], pos[i + 1], pos[j], pos[j + 1])) return null;
    }
  }
  return pos;
}

/**
 * Given a grid, assign each letter of every word to a distinct grid cell,
 * ensuring no segment of a word's path crosses an earlier segment of that word.
 */
function assignWords(grid, words) {
  const letterCells = {};
  for (let r = 0; r < GRID_SIZE; r++) {
    for (let c = 0; c < GRID_SIZE; c++) {
      const ch = grid[r][c];
      if (!letterCells[ch]) letterCells[ch] = [];
      letterCells[ch].push([r, c]);
    }
  }

  const placements = {};
  for (const word of words) {
    const positions = findNonCrossingPath(word, letterCells);
    if (!positions) return null;
    placements[word] = { positions };
  }
  return placements;
}

/**
 * Main entry point. Returns { grid, placements, orderedWords } on success,
 * or { error: string } if the words cannot fit.
 */
function generate(words) {
  const required = computeRequired(words);
  const totalRequired = Object.values(required).reduce((s, v) => s + v, 0);

  if (totalRequired > GRID_CELLS) {
    // Build a human-readable breakdown of the bottleneck letters
    const breakdown = Object.entries(required)
      .sort((a, b) => b[1] - a[1])
      .map(([ch, cnt]) => `${ch}×${cnt}`)
      .join(', ');
    return {
      error:
        `The words collectively require at least ${totalRequired} letter cells ` +
        `(${breakdown}), but the grid only has ${GRID_CELLS}. ` +
        `Try fewer words or words with more shared letters.`,
    };
  }

  // Run a few times so the layout looks different on each generation
  for (let attempt = 0; attempt < 50; attempt++) {
    const cells = buildCells(required);
    const grid = [];
    for (let r = 0; r < GRID_SIZE; r++)
      grid.push(cells.slice(r * GRID_SIZE, (r + 1) * GRID_SIZE));

    const placements = assignWords(grid, words);
    if (placements) return { grid, placements, orderedWords: words };
  }

  // Fallback (should be unreachable)
  return { error: 'Unexpected failure. Please try again.' };
}

// ── Rendering ──────────────────────────────────────────────────────────────────

const PATH_COLOR = '#ef4444'; // red — used for the connecting line and dot circles

let currentResult    = null;
let selectedWord     = null;
let currentCellColorMap = {};
let dotsMode         = false;

function renderAll(result) {
  currentResult = result;
  selectedWord  = null;
  document.getElementById('word-path').innerHTML = '';

  const { grid, placements, orderedWords } = result;

  // Each cell gets the color of the first word (by palette order) that uses it
  currentCellColorMap = {};
  [...orderedWords].reverse().forEach((word, i) => {
    const color = PALETTE[(orderedWords.length - 1 - i) % PALETTE.length];
    placements[word].positions.forEach(([r, c]) => {
      currentCellColorMap[`${r},${c}`] = color;
    });
  });

  renderGrid(grid, currentCellColorMap);
  renderWordList(orderedWords, placements);
  applyDotsMode(); // honour toggle state across re-generates
  document.getElementById('print-btn').style.display = 'inline-block';
}

/** Applies or removes dots-mode appearance for every cell, then redraws SVG. */
function applyDotsMode() {
  if (!currentResult) return;
  const { grid } = currentResult;
  for (let r = 0; r < GRID_SIZE; r++) {
    for (let c = 0; c < GRID_SIZE; c++) {
      const cell = document.getElementById(`cell-${r}-${c}`);
      if (!cell) continue;
      if (dotsMode) {
        cell.textContent = '';        // dot drawn in SVG instead
        cell.style.background = '';
        cell.style.color = '';
        cell.style.fontSize = '';
      } else {
        cell.textContent = grid[r][c];
        cell.style.fontSize = '';
        const isActive = selectedWord &&
          currentResult.placements[selectedWord].positions.some(([pr, pc]) => pr === r && pc === c);
        const color = isActive
          ? PALETTE[currentResult.orderedWords.indexOf(selectedWord) % PALETTE.length]
          : null;
        cell.style.background = color ? color.bg : '';
        cell.style.color      = color ? color.fg : '';
      }
    }
  }
  document.querySelectorAll('.word-directions').forEach(el => {
    el.textContent = dotsMode ? el.dataset.unlabeled : el.dataset.labeled;
  });

  redrawSVG();
}

function renderGrid(grid, cellColorMap) {
  const container = document.getElementById('grid');
  container.innerHTML = '';

  for (let r = 0; r < GRID_SIZE; r++) {
    for (let c = 0; c < GRID_SIZE; c++) {
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.id = `cell-${r}-${c}`;
      cell.textContent = grid[r][c];

      const color = cellColorMap[`${r},${c}`];
      if (color) {
        cell.style.background = color.bg;
        cell.style.color = color.fg;
      }

      container.appendChild(cell);
    }
  }
}

const NAV_DIRS = [
  [-1, 0,'N'], [1, 0,'S'], [0, 1,'E'], [0,-1,'W'],
  [-1, 1,'NE'],[1, 1,'SE'],[1,-1,'SW'],[-1,-1,'NW'],
];

function isNavPos(r, c) {
  if (r === START_POS[0] && c === START_POS[1]) return true;
  if (r === END_POS[0]   && c === END_POS[1])   return true;
  return r >= 0 && r < GRID_SIZE && c >= 0 && c < GRID_SIZE;
}

/** BFS tile-by-tile path from (r1,c1) to (r2,c2), respecting wall blocks. */
function navBFS(r1, c1, r2, c2) {
  if (r1 === r2 && c1 === c2) return [];
  const queue = [[r1, c1, []]];
  const visited = new Set([`${r1},${c1}`]);
  while (queue.length) {
    const [r, c, path] = queue.shift();
    for (const [dr, dc, dir] of NAV_DIRS) {
      const nr = r + dr, nc = c + dc;
      if (!isNavPos(nr, nc) || visited.has(`${nr},${nc}`)) continue;
      const newPath = [...path, dir];
      if (nr === r2 && nc === c2) return newPath;
      visited.add(`${nr},${nc}`);
      queue.push([nr, nc, newPath]);
    }
  }
  return [];
}

/** Convert a flat step array into compressed direction strings (e.g. ['N','N','N'] → 'N 3'). */
function compressSteps(steps) {
  const out = [];
  for (let i = 0; i < steps.length; ) {
    const d = steps[i];
    const isDiag = d.length === 2;
    if (isDiag) { out.push(`1 ${d}`); i++; continue; }
    let k = i + 1;
    while (k < steps.length && steps[k] === d) k++;
    out.push(`${k - i} ${d}`);
    i = k;
  }
  return out;
}

function computeWordDirections(word, positions) {
  const waypoints = [START_POS, ...positions, END_POS];
  const segments = [];
  for (let i = 0; i < waypoints.length - 1; i++) {
    const [r1, c1] = waypoints[i];
    const [r2, c2] = waypoints[i + 1];
    segments.push(compressSteps(navBFS(r1, c1, r2, c2)).join(', '));
  }
  return segments;
}

function renderWordList(orderedWords, placements) {
  const container = document.getElementById('word-list');
  container.innerHTML = '';

  orderedWords.forEach((word, i) => {
    const color = PALETTE[i % PALETTE.length];
    const p = placements[word];

    const card = document.createElement('div');
    card.className = 'word-card';
    card.style.background = color.bg;
    card.style.color = color.fg;
    card.dataset.word = word;

    const nameEl = document.createElement('div');
    nameEl.className = 'word-name';
    nameEl.textContent = word;

    const dirsEl = document.createElement('div');
    dirsEl.className = 'word-directions';
    const dirSteps = computeWordDirections(word, p.positions);
    const targets = [...word, 'END'];
    const last = dirSteps.length - 1;
    dirsEl.dataset.labeled   = dirSteps.map((s, i) => i === last ? `Finish: ${s}` : `${i+1}. ${targets[i]}: ${s}`).join('\n');
    dirsEl.dataset.unlabeled = dirSteps.map((s, i) => i === last ? `Finish: ${s}` : `${i+1}. ${s}`).join('\n');
    dirsEl.textContent = dotsMode ? dirsEl.dataset.unlabeled : dirsEl.dataset.labeled;

    card.append(nameEl, dirsEl);
    card.addEventListener('click', () => toggleWordHighlight(word, card));
    container.appendChild(card);
  });
}

/** Returns the center of el in SVG-local coordinates. */
function getCenter(el) {
  const svgRect = document.getElementById('word-path').getBoundingClientRect();
  const r = el.getBoundingClientRect();
  return { x: r.left + r.width / 2 - svgRect.left, y: r.top + r.height / 2 - svgRect.top };
}

/**
 * Single source of truth for all SVG drawing.
 * - In dots mode: draws a red circle for every cell (dimmed for non-word cells
 *   when a word is selected).
 * - When a word is selected: draws the connecting line (and, in normal mode,
 *   small filled dots at each waypoint).
 */
function redrawSVG() {
  const svg = document.getElementById('word-path');
  if (!svg) return;
  svg.innerHTML = '';
  if (!currentResult) return;

  // Draw static walls connecting tile pairs
  // In letter mode: clip at circle edge. In dots mode: connect to dot center.
  const sampleCell = document.getElementById('cell-0-0');
  const cellVisualRadius = sampleCell ? sampleCell.getBoundingClientRect().width / 2 : 18;
  for (const [t1, t2] of WALLS) {
    const r1 = Math.floor((t1 - 1) / GRID_SIZE), c1 = (t1 - 1) % GRID_SIZE;
    const r2 = Math.floor((t2 - 1) / GRID_SIZE), c2 = (t2 - 1) % GRID_SIZE;
    const p1 = getCenter(document.getElementById(`cell-${r1}-${c1}`));
    const p2 = getCenter(document.getElementById(`cell-${r2}-${c2}`));
    const WALL_R = dotsMode ? 10 : cellVisualRadius;
    const dx = p2.x - p1.x, dy = p2.y - p1.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist < WALL_R * 2) continue;
    const ux = dx / dist, uy = dy / dist;
    const wall = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    wall.setAttribute('x1', (p1.x + ux * WALL_R).toFixed(1));
    wall.setAttribute('y1', (p1.y + uy * WALL_R).toFixed(1));
    wall.setAttribute('x2', (p2.x - ux * WALL_R).toFixed(1));
    wall.setAttribute('y2', (p2.y - uy * WALL_R).toFixed(1));
    wall.setAttribute('stroke', '#1e293b');
    wall.setAttribute('stroke-width', '7');
    wall.setAttribute('stroke-linecap', 'round');
    svg.appendChild(wall);
  }

  if (dotsMode) {
    const wordCells = selectedWord
      ? new Set(currentResult.placements[selectedWord].positions.map(([r, c]) => `${r},${c}`))
      : null;

    for (let r = 0; r < GRID_SIZE; r++) {
      for (let c = 0; c < GRID_SIZE; c++) {
        const p          = getCenter(document.getElementById(`cell-${r}-${c}`));
        const isWordCell = wordCells && wordCells.has(`${r},${c}`);
        const circle     = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        circle.setAttribute('cx', p.x.toFixed(1));
        circle.setAttribute('cy', p.y.toFixed(1));
        circle.setAttribute('r', '10');
        // All dots are dark grey and filled
        circle.setAttribute('fill', '#4b5563');
        circle.setAttribute('stroke', 'none');
        svg.appendChild(circle);

        if (isWordCell) {
          // Red ring with a small gap around the filled dot
          const ring = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
          ring.setAttribute('cx', p.x.toFixed(1));
          ring.setAttribute('cy', p.y.toFixed(1));
          ring.setAttribute('r', '15');
          ring.setAttribute('fill', 'none');
          ring.setAttribute('stroke', PATH_COLOR);
          ring.setAttribute('stroke-width', '2');
          svg.appendChild(ring);
        }
      }
    }
  }

  if (!selectedWord) return;

  const positions = currentResult.placements[selectedWord].positions;
  const pts = [
    getCenter(document.getElementById('start-box')),
    ...positions.map(([r, c]) => getCenter(document.getElementById(`cell-${r}-${c}`))),
    getCenter(document.getElementById('end-box')),
  ];

  // Compute clipped segment endpoints (ring-clipped at each waypoint).
  const RING_R = 15;
  const segPts = [];
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i], b = pts[i + 1];
    const rA = i === 0              ? 0 : RING_R;
    const rB = i === pts.length - 2 ? 0 : RING_R;
    const dx = b.x - a.x, dy = b.y - a.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    if (dist < rA + rB) continue;
    const ux = dx / dist, uy = dy / dist;
    segPts.push({ x1: a.x + ux * rA, y1: a.y + uy * rA,
                  x2: b.x - ux * rB, y2: b.y - uy * rB });
  }

  // Draw segments in order; earlier segments get gaps where later ones cross over them.
  const BRIDGE_GAP = 6; // px cleared on each side of a crossing
  for (let i = 0; i < segPts.length; i++) {
    const s = segPts[i];
    const dx = s.x2 - s.x1, dy = s.y2 - s.y1;
    const len = Math.sqrt(dx * dx + dy * dy);
    if (len < 1) continue;

    // Collect t-values where earlier segments cross this one
    const crossTs = [];
    for (let j = 0; j < i; j++) {
      const t = segIntersectT(s.x1, s.y1, s.x2, s.y2,
                              segPts[j].x1, segPts[j].y1, segPts[j].x2, segPts[j].y2);
      if (t !== null) crossTs.push(t);
    }
    crossTs.sort((a, b) => a - b);

    // Build path with gaps at each crossing
    let d = '', cur = 0;
    for (const t of crossTs) {
      const gT = BRIDGE_GAP / len;
      const tEnd = Math.max(0, t - gT);
      if (tEnd > cur + 1e-4) {
        d += `M${(s.x1 + cur * dx).toFixed(1)},${(s.y1 + cur * dy).toFixed(1)} ` +
             `L${(s.x1 + tEnd * dx).toFixed(1)},${(s.y1 + tEnd * dy).toFixed(1)} `;
      }
      cur = Math.min(1, t + gT);
    }
    if (cur < 1 - 1e-4) {
      d += `M${(s.x1 + cur * dx).toFixed(1)},${(s.y1 + cur * dy).toFixed(1)} ` +
           `L${s.x2.toFixed(1)},${s.y2.toFixed(1)}`;
    }
    if (!d.trim()) continue;

    const seg = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    seg.setAttribute('d', d);
    seg.setAttribute('stroke', PATH_COLOR);
    seg.setAttribute('stroke-width', '2.5');
    seg.setAttribute('stroke-opacity', '0.75');
    seg.setAttribute('fill', 'none');
    seg.setAttribute('stroke-linecap', 'round');
    svg.appendChild(seg);
  }

}

function toggleWordHighlight(word, cardEl) {
  if (selectedWord === word) {
    selectedWord = null;
    document.querySelectorAll('.word-card').forEach(c => c.classList.remove('selected'));
  } else {
    selectedWord = word;
    document.querySelectorAll('.word-card').forEach(c => c.classList.remove('selected'));
    cardEl.classList.add('selected');
  }
  applyDotsMode();
}

// ── Print mode ─────────────────────────────────────────────────────────────────

function buildPrintHTML(result) {
  const { grid, placements, orderedWords } = result;

  // SVG layout constants (mirrors the CSS grid proportions)
  const PC = 56, PG = 8, PS = PC + PG; // cell, gap, step
  const PR = Math.round(PC * 0.36);    // visual circle radius (~20px)
  const SVG_W = 6 * PS + PC, SVG_H = SVG_W;

  function cc(r, c) { return { x: c * PS + PC / 2, y: (r + 1) * PS + PC / 2 }; }
  const CS = { x: 2 * PS + PC / 2, y: PC / 2 };       // start center
  const CE = { x: 5 * PS + PC / 2, y: 3 * PS + PC / 2 }; // end center

  function svgWalls(wallR = PR) {
    return WALLS.map(([t1, t2]) => {
      const r1 = Math.floor((t1-1)/5), c1 = (t1-1)%5;
      const r2 = Math.floor((t2-1)/5), c2 = (t2-1)%5;
      const p1 = cc(r1,c1), p2 = cc(r2,c2);
      const dx = p2.x-p1.x, dy = p2.y-p1.y, d = Math.sqrt(dx*dx+dy*dy);
      const ux = dx/d, uy = dy/d;
      return `<line x1="${(p1.x+ux*wallR).toFixed(1)}" y1="${(p1.y+uy*wallR).toFixed(1)}" x2="${(p2.x-ux*wallR).toFixed(1)}" y2="${(p2.y-uy*wallR).toFixed(1)}" stroke="#1e293b" stroke-width="5" stroke-linecap="round"/>`;
    }).join('');
  }

  function svgCells(showLetters, activeSet) {
    let s = '';
    for (let r = 0; r < 5; r++) {
      for (let c = 0; c < 5; c++) {
        const p = cc(r, c);
        const active = activeSet && activeSet.has(`${r},${c}`);
        if (showLetters) {
          s += `<circle cx="${p.x}" cy="${p.y}" r="${PR}" fill="#f1f5f9" stroke="#cbd5e1" stroke-width="1.5"/>`;
          s += `<text x="${p.x}" y="${p.y}" text-anchor="middle" dominant-baseline="central" font-family="Menlo,Consolas,monospace" font-weight="800" font-size="18" fill="#0f172a">${grid[r][c]}</text>`;
        } else {
          s += `<circle cx="${p.x}" cy="${p.y}" r="11" fill="#4b5563"/>`;
          if (active)
            s += `<circle cx="${p.x}" cy="${p.y}" r="13" fill="none" stroke="#ef4444" stroke-width="2"/>`;
        }
      }
    }
    return s;
  }

  function svgMarkers() {
    return [
      `<circle cx="${CS.x}" cy="${CS.y}" r="${PR}" fill="#f1f5f9" stroke="#94a3b8" stroke-width="1.5"/>`,
      `<text x="${CS.x}" y="${CS.y+4}" text-anchor="middle" font-size="12" fill="#64748b">▲</text>`,
      `<text x="${CS.x}" y="${CS.y-PR-3}" text-anchor="middle" font-family="sans-serif" font-size="7" fill="#64748b">START</text>`,
      `<circle cx="${CE.x}" cy="${CE.y}" r="${PR}" fill="#f1f5f9" stroke="#94a3b8" stroke-width="1.5"/>`,
      `<circle cx="${CE.x}" cy="${CE.y}" r="8" fill="none" stroke="#64748b" stroke-width="1.5"/>`,
      `<circle cx="${CE.x}" cy="${CE.y}" r="2.5" fill="#64748b"/>`,
      `<text x="${CE.x}" y="${CE.y+PR+8}" text-anchor="middle" font-family="sans-serif" font-size="7" fill="#64748b">END</text>`,
    ].join('');
  }

  function svgPath(word) {
    const pts = [CS, ...placements[word].positions.map(([r,c]) => cc(r,c)), CE];
    const RR = 13, BRIDGE_GAP = 6;

    // Build clipped segment endpoints (ring-clipped at each waypoint)
    const segs = [];
    for (let i = 0; i < pts.length - 1; i++) {
      const a = pts[i], b = pts[i+1];
      const rA = i === 0 ? 0 : RR, rB = i === pts.length-2 ? 0 : RR;
      const dx = b.x-a.x, dy = b.y-a.y, dist = Math.sqrt(dx*dx+dy*dy);
      if (dist < rA+rB) continue;
      const ux = dx/dist, uy = dy/dist;
      segs.push({ x1: a.x+ux*rA, y1: a.y+uy*rA, x2: b.x-ux*rB, y2: b.y-uy*rB });
    }

    // Draw each segment with gaps where later segments cross over it
    let out = '';
    for (let i = 0; i < segs.length; i++) {
      const s = segs[i];
      const dx = s.x2-s.x1, dy = s.y2-s.y1, len = Math.sqrt(dx*dx+dy*dy);
      if (len < 1) continue;
      const crossTs = [];
      for (let j = 0; j < i; j++) {
        const t = segIntersectT(s.x1, s.y1, s.x2, s.y2, segs[j].x1, segs[j].y1, segs[j].x2, segs[j].y2);
        if (t !== null) crossTs.push(t);
      }
      crossTs.sort((a, b) => a - b);
      let d = '', cur = 0;
      for (const t of crossTs) {
        const gT = BRIDGE_GAP / len;
        const tEnd = Math.max(0, t - gT);
        if (tEnd > cur + 1e-4)
          d += `M${(s.x1+cur*dx).toFixed(1)},${(s.y1+cur*dy).toFixed(1)} L${(s.x1+tEnd*dx).toFixed(1)},${(s.y1+tEnd*dy).toFixed(1)} `;
        cur = Math.min(1, t + gT);
      }
      if (cur < 1 - 1e-4)
        d += `M${(s.x1+cur*dx).toFixed(1)},${(s.y1+cur*dy).toFixed(1)} L${s.x2.toFixed(1)},${s.y2.toFixed(1)}`;
      if (d.trim())
        out += `<path d="${d.trim()}" stroke="#ef4444" stroke-width="2.5" stroke-opacity="0.8" fill="none" stroke-linecap="round"/>`;
    }
    return out;
  }

  function svgCompass() {
    const cx = SVG_W - 36, cy = 36, R = 22, arm = 14, tip = 7;
    return [
      `<circle cx="${cx}" cy="${cy}" r="${R}" fill="white" stroke="#cbd5e1" stroke-width="1.5"/>`,
      // N/S spine — north half dark, south half light
      `<polygon points="${cx},${cy-arm} ${cx-tip/2},${cy} ${cx+tip/2},${cy}" fill="#1e293b"/>`,
      `<polygon points="${cx},${cy+arm} ${cx-tip/2},${cy} ${cx+tip/2},${cy}" fill="#cbd5e1"/>`,
      // E/W spine
      `<line x1="${cx-arm}" y1="${cy}" x2="${cx+arm}" y2="${cy}" stroke="#94a3b8" stroke-width="1.5"/>`,
      // Labels
      `<text x="${cx}" y="${cy-R+8}" text-anchor="middle" font-family="sans-serif" font-weight="700" font-size="9" fill="#1e293b">N</text>`,
      `<text x="${cx}" y="${cy+R-2}" text-anchor="middle" font-family="sans-serif" font-size="8" fill="#94a3b8">S</text>`,
      `<text x="${cx+R-4}" y="${cy+3}" text-anchor="middle" font-family="sans-serif" font-size="8" fill="#94a3b8">E</text>`,
      `<text x="${cx-R+4}" y="${cy+3}" text-anchor="middle" font-family="sans-serif" font-size="8" fill="#94a3b8">W</text>`,
    ].join('');
  }

  function buildSVG(showLetters, pathWord, activePositions) {
    const activeSet = activePositions ? new Set(activePositions.map(([r,c]) => `${r},${c}`)) : null;
    const gridCenterX = (4 * PS + PC) / 2;
    const svgCenterX = SVG_W / 2;
    const shiftPx = Math.round((svgCenterX - gridCenterX) * 540 / SVG_W);
    return `<svg width="${SVG_W}" height="${SVG_H}" style="max-width:540px;height:auto;margin-left:${shiftPx}px">`
      + svgCells(showLetters, activeSet)
      + svgWalls(showLetters ? PR : 11)
      + svgMarkers()
      + svgCompass()
      + (pathWord ? svgPath(pathWord) : '')
      + `</svg>`;
  }

  const css = `
    *{box-sizing:border-box;margin:0;padding:0}
    body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#0f172a;background:#fff}
    .page{padding:2rem 2.5rem;page-break-after:always}
    .page:last-child{page-break-after:avoid}
    h1{font-size:1.25rem;font-weight:800;border-bottom:2px solid #e2e8f0;padding-bottom:.5rem;margin-bottom:1.25rem}
    .badge{font-size:.8rem;font-weight:400;color:#94a3b8;margin-left:.5rem}
    .layout{display:flex;gap:2rem;align-items:flex-start;flex-wrap:wrap}
    .key{flex:1;min-width:180px}
    .key-item{margin-bottom:1rem}
    .key-label{font-size:.65rem;text-transform:uppercase;letter-spacing:.08em;color:#64748b;margin-bottom:.2rem}
    .runner-page{display:flex;flex-direction:column;align-items:center}
    .steps{font-family:Menlo,Consolas,monospace;font-size:.75rem;color:#334155;width:fit-content;margin-top:1rem}
    .step{display:flex;align-items:baseline;gap:.4rem;padding:.3rem 0;border-bottom:1px solid #f1f5f9}
    .step-dirs{white-space:nowrap}
    .write-blank{display:inline-block;width:1.75rem;border-bottom:1.5px solid #94a3b8;flex-shrink:0}
    .letter-boxes{display:flex;gap:.6rem;flex-wrap:wrap;margin-top:1.25rem;justify-content:center}
    .letter-box{display:flex;flex-direction:column;align-items:center;gap:.25rem}
    .letter-box-square{width:3.25rem;height:3.25rem;border:2px solid #334155;border-radius:4px}
    .letter-box-num{font-size:.6rem;color:#94a3b8;font-family:sans-serif}
    @media print{.page{padding:1cm 1.5cm}@page{margin:0}}
  `;

  let html = `<!DOCTYPE html><html><head><meta charset="utf-8"><title>Mazeo Print</title><style>${css}</style></head><body>`;

  // ── 1. Maze Coordinator ──
  html += `<div class="page"><h1>Maze Coordinator</h1><div class="runner-page">${buildSVG(true, null, null)}<div style="display:flex;gap:1.5rem;flex-wrap:wrap;justify-content:center;margin-top:1.25rem">`;
  orderedWords.forEach((word, i) => {
    html += `<div class="key-label">#${i+1}: ${word}</div>`;
  });
  html += `</div></div></div>`;

  // ── 2. Maze Runner – Easy (one per word) ──
  orderedWords.forEach((word, i) => {
    const boxes = word.split('').map((_, j) =>
      `<div class="letter-box"><div class="letter-box-square"></div><div class="letter-box-num">${j+1}</div></div>`
    ).join('');
    html += `<div class="page"><h1>Maze Runner &ndash; Easy<span class="badge">#${i+1} of ${orderedWords.length}</span></h1>`
          + `<div class="runner-page">`
          + buildSVG(false, word, placements[word].positions)
          + `<div class="letter-boxes">${boxes}</div>`
          + `</div></div>`;
  });

  // ── 3. Maze Runner – Hard (one per word) ──
  orderedWords.forEach((word, i) => {
    const dirs = computeWordDirections(word, placements[word].positions);
    const boxes = word.split('').map((_, j) =>
      `<div class="letter-box"><div class="letter-box-square"></div><div class="letter-box-num">${j+1}</div></div>`
    ).join('');
    html += `<div class="page"><h1>Maze Runner &ndash; Hard<span class="badge">#${i+1} of ${orderedWords.length}</span></h1>`
          + `<div class="runner-page">`
          + buildSVG(false, null, null)
          + `<div class="key-label" style="margin-top:1rem">Steps</div>`
          + `<div class="steps">${dirs.map((s,j) => j === dirs.length-1
              ? `<div class="step"><span class="step-dirs">Finish: ${s}</span></div>`
              : `<div class="step"><span class="step-dirs">${j+1}. ${s}</span></div>`
            ).join('')}</div>`
          + `<div class="letter-boxes">${boxes}</div>`
          + `</div></div>`;
  });

  html += `</body></html>`;
  return html;
}

function openPrintWindow() {
  if (!currentResult) return;
  const w = window.open('', '_blank');
  w.document.write(buildPrintHTML(currentResult));
  w.document.close();
}

// ── Input handling ─────────────────────────────────────────────────────────────

function showError(msg) {
  const el = document.getElementById('error-msg');
  el.textContent = msg;
  el.style.display = 'block';
}

function clearError() {
  const el = document.getElementById('error-msg');
  el.style.display = 'none';
  el.textContent = '';
}

document.getElementById('print-btn').addEventListener('click', openPrintWindow);

document.getElementById('generate-btn').addEventListener('click', () => {
  clearError();

  const raw = document.getElementById('words-input').value;
  const words = [...new Set(
    raw.split('\n')
       .map(w => w.trim().toUpperCase().replace(/[^A-Z]/g, ''))
       .filter(w => w.length > 0)
  )];

  if (words.length === 0) {
    showError('Please enter at least one word.');
    return;
  }

  if (words.length > 4) {
    showError('Please enter 4 words or fewer.');
    return;
  }

  if (words.some(w => w.length > 8)) {
    showError('Words must be 8 letters or fewer.');
    return;
  }

  const result = generate(words);
  if (result.error) {
    showError(result.error);
    return;
  }

  const output = document.getElementById('output');
  output.classList.add('visible');
  renderAll(result);
  document.getElementById('generate-btn').textContent = 'Regenerate Maze';
  output.scrollIntoView({ behavior: 'smooth', block: 'start' });
});

document.getElementById('words-input').addEventListener('keydown', e => {
  if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
    document.getElementById('generate-btn').click();
  }
});

document.getElementById('dots-toggle').addEventListener('change', e => {
  dotsMode = e.target.checked;
  applyDotsMode();
});
