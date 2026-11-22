(() => {
  'use strict';

  const GRID_SIZE = 5;
  const GRID_CELLS = GRID_SIZE * GRID_SIZE; // 25
  const MAX_WORDS = 4;
  const MAX_WORD_LENGTH = 8;
  const MAX_BT_NODES = 5000;
  const PATH_COLOR = '#ef4444';

  // Walls between adjacent tiles (1-indexed, top-to-bottom left-to-right)
  const WALLS = [
    [1, 2], [3, 4], [7, 8], [9, 10], [13, 14], [16, 17], [22, 23], // horizontal
    [1, 6], [6, 11], [7, 12], [13, 18], [19, 24], [20, 25],        // vertical
  ];

  // Virtual grid positions for start/end boxes (row, col in extended grid space)
  // Start-box sits one row below col 2; end-box sits one col right of row 2.
  const START_POS = [5, 2];
  const END_POS = [2, 5];

  function tileToRC(tile) {
    return [Math.floor((tile - 1) / GRID_SIZE), (tile - 1) % GRID_SIZE];
  }

  // Pre-compute blocked orthogonal edges from WALLS
  const BLOCKED_EDGES = new Set();
  for (const [t1, t2] of WALLS) {
    const [r1, c1] = tileToRC(t1);
    const [r2, c2] = tileToRC(t2);
    BLOCKED_EDGES.add(`${r1},${c1}|${r2},${c2}`);
    BLOCKED_EDGES.add(`${r2},${c2}|${r1},${c1}`);
  }

  // Distinct, accessible color pairs (WCAG AA contrast >= 4.5:1)
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

  function escapeHtml(str) {
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  // ── Geometry helpers (shared by solver, live SVG, and print SVG) ───────────────

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
    const d1 = cross2d(p3, p4, p1);
    const d2 = cross2d(p3, p4, p2);
    const d3 = cross2d(p1, p2, p3);
    const d4 = cross2d(p1, p2, p4);
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
    for (const [ch, cnt] of Object.entries(required)) {
      for (let i = 0; i < cnt; i++) cells.push(ch);
    }
    while (cells.length < GRID_CELLS) {
      cells.push(ALPHA[Math.floor(Math.random() * 26)]);
    }
    return shuffle(cells);
  }

  /**
   * Assign cells to each letter of `word` via bounded backtracking.
   * Candidates are tried farthest-first (for spread), skipping any candidate
   * whose incoming segment crosses or doubles back over an earlier segment.
   * Returns the positions array, or null if no valid assignment is found.
   */
  function findNonCrossingPath(word, letterCells) {
    const used = new Set();
    const pos = [];
    let visitedNodes = 0;

    function wouldCross(candidate) {
      if (pos.length < 2) return false;
      const prev = pos[pos.length - 1];
      for (let i = 0; i < pos.length - 2; i++) {
        if (segmentsIntersect(prev, candidate, pos[i], pos[i + 1])) return true;
      }
      // Check collinear overlap with the immediately preceding segment (both
      // T-intersections and 180-degree reversals past penult).
      const penult = pos[pos.length - 2];
      if (cross2d(penult, prev, candidate) === 0 &&
          (onSegment(candidate, penult, prev) || onSegment(penult, prev, candidate))) {
        return true;
      }
      return false;
    }

    function bt(idx) {
      if (idx === word.length) return true;
      if (++visitedNodes > MAX_BT_NODES) return false;
      const ch = word[idx];

      const candidates = (letterCells[ch] || [])
        .filter(p => !used.has(`${p[0]},${p[1]}`));
      if (candidates.length === 0) return false;

      // Shuffle for variety, then sort farthest-first from the previous letter
      shuffle(candidates);
      if (pos.length > 0) {
        const [pr, pc] = pos[pos.length - 1];
        candidates.sort((a, b) =>
          (b[0] - pr) ** 2 + (b[1] - pc) ** 2 - (a[0] - pr) ** 2 - (a[1] - pc) ** 2
        );
      }

      for (const p of candidates) {
        if (wouldCross(p)) continue;
        const key = `${p[0]},${p[1]}`;
        used.add(key);
        pos.push(p);
        if (bt(idx + 1)) return true;
        pos.pop();
        used.delete(key);
      }
      return false;
    }

    if (!bt(0)) return null;

    // Final validation: confirm no two non-adjacent segments cross
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

    for (let attempt = 0; attempt < 50; attempt++) {
      const cells = buildCells(required);
      const grid = [];
      for (let r = 0; r < GRID_SIZE; r++) {
        grid.push(cells.slice(r * GRID_SIZE, (r + 1) * GRID_SIZE));
      }

      const placements = assignWords(grid, words);
      if (placements) return { grid, placements, orderedWords: words };
    }

    return {
      error: 'Could not arrange non-crossing paths for these words. Try generating again or using fewer or shorter words.',
    };
  }

  // ── Navigation / Directions ────────────────────────────────────────────────────

  const NAV_DIRS = [
    [-1, 0, 'N'], [1, 0, 'S'], [0, 1, 'E'], [0, -1, 'W'],
    [-1, 1, 'NE'], [1, 1, 'SE'], [1, -1, 'SW'], [-1, -1, 'NW'],
  ];

  function isNavPos(r, c, targetR, targetC) {
    // Allow START_POS / END_POS only when it is the destination, not as an intermediate transit tile
    if (r === targetR && c === targetC) {
      if ((r === START_POS[0] && c === START_POS[1]) ||
          (r === END_POS[0] && c === END_POS[1])) {
        return true;
      }
    }
    return r >= 0 && r < GRID_SIZE && c >= 0 && c < GRID_SIZE;
  }

  /**
   * BFS tile-by-tile path from (r1,c1) to (r2,c2), respecting orthogonal wall blocks.
   * Diagonal moves remain open so corner tiles enclosed by orthogonal walls stay reachable.
   */
  function navBFS(r1, c1, r2, c2) {
    if (r1 === r2 && c1 === c2) return [];
    const queue = [[r1, c1, []]];
    const visited = new Set([`${r1},${c1}`]);
    while (queue.length) {
      const [r, c, path] = queue.shift();
      for (const [dr, dc, dir] of NAV_DIRS) {
        const nr = r + dr;
        const nc = c + dc;
        if (!isNavPos(nr, nc, r2, c2) || visited.has(`${nr},${nc}`)) continue;
        if (BLOCKED_EDGES.has(`${r},${c}|${nr},${nc}`)) continue;
        const newPath = [...path, dir];
        if (nr === r2 && nc === c2) return newPath;
        visited.add(`${nr},${nc}`);
        queue.push([nr, nc, newPath]);
      }
    }
    return [];
  }

  /**
   * Convert a flat step array into compressed direction strings (e.g. ['N','N','N'] → '3 N').
   * Diagonal moves are kept as individual steps ('1 NE') so compass turns stay easy to follow.
   */
  function compressSteps(steps) {
    const out = [];
    for (let i = 0; i < steps.length;) {
      const d = steps[i];
      if (d.length === 2) {
        out.push(`1 ${d}`);
        i++;
        continue;
      }
      let k = i + 1;
      while (k < steps.length && steps[k] === d) k++;
      out.push(`${k - i} ${d}`);
      i = k;
    }
    return out;
  }

  function computeWordDirections(positions) {
    const waypoints = [START_POS, ...positions, END_POS];
    const segments = [];
    for (let i = 0; i < waypoints.length - 1; i++) {
      const [r1, c1] = waypoints[i];
      const [r2, c2] = waypoints[i + 1];
      segments.push(compressSteps(navBFS(r1, c1, r2, c2)).join(', '));
    }
    return segments;
  }

  // ── Rendering ──────────────────────────────────────────────────────────────────

  let currentResult = null;
  let selectedWord = null;
  let currentCellColorMap = {};
  let dotsMode = false;
  let lastGeneratedRaw = '';

  function renderAll(result) {
    currentResult = result;
    selectedWord = null;
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

    renderGrid(grid);
    renderWordList(orderedWords, placements);
    applyDotsMode();
    document.getElementById('copy-link-btn').style.display = 'inline-block';
    document.getElementById('print-btn').style.display = 'inline-block';
    document.getElementById('stale-banner').classList.remove('visible');
  }

  /** Applies letter/dots mode and selection highlighting to every cell, then redraws SVG. */
  function applyDotsMode() {
    if (!currentResult) return;
    const { grid, placements, orderedWords } = currentResult;

    const selectedPositions = selectedWord ? placements[selectedWord].positions : null;
    const selectedColor = selectedWord
      ? PALETTE[orderedWords.indexOf(selectedWord) % PALETTE.length]
      : null;

    const stepByKey = new Map();
    if (selectedPositions) {
      selectedPositions.forEach(([r, c], idx) => {
        stepByKey.set(`${r},${c}`, idx + 1);
      });
    }

    for (let r = 0; r < GRID_SIZE; r++) {
      for (let c = 0; c < GRID_SIZE; c++) {
        const cell = document.getElementById(`cell-${r}-${c}`);
        if (!cell) continue;
        const key = `${r},${c}`;
        const stepNum = stepByKey.get(key) || 0;
        const letter = grid[r][c];

        if (dotsMode) {
          cell.textContent = '';
          cell.classList.add('dots-hidden');
          cell.style.background = '';
          cell.style.color = '';
          cell.style.borderColor = '';
          cell.setAttribute(
            'aria-label',
            stepNum
              ? `Row ${r + 1}, Column ${c + 1}, step ${stepNum} of ${selectedWord}`
              : `Row ${r + 1}, Column ${c + 1}`
          );
        } else {
          cell.classList.remove('dots-hidden');
          cell.textContent = letter;
          const color = selectedWord
            ? (stepNum ? selectedColor : null)
            : (currentCellColorMap[key] || null);
          cell.style.background = color ? color.bg : '';
          cell.style.color = color ? color.fg : '';
          cell.style.borderColor = color ? color.fg : '';
          cell.setAttribute(
            'aria-label',
            stepNum
              ? `Row ${r + 1}, Column ${c + 1}: ${letter}, step ${stepNum} of ${selectedWord}`
              : `Row ${r + 1}, Column ${c + 1}: ${letter}`
          );
        }
      }
    }

    document.querySelectorAll('.word-directions').forEach(el => {
      el.textContent = dotsMode ? el.dataset.unlabeled : el.dataset.labeled;
    });

    redrawSVG();
  }

  function renderGrid(grid) {
    const container = document.getElementById('grid');
    container.innerHTML = '';

    for (let r = 0; r < GRID_SIZE; r++) {
      for (let c = 0; c < GRID_SIZE; c++) {
        const cell = document.createElement('div');
        cell.className = 'cell';
        cell.id = `cell-${r}-${c}`;
        cell.textContent = grid[r][c];
        container.appendChild(cell);
      }
    }
  }

  function renderWordList(orderedWords, placements) {
    const container = document.getElementById('word-list');
    container.innerHTML = '';

    orderedWords.forEach((word, i) => {
      const color = PALETTE[i % PALETTE.length];
      const p = placements[word];

      const card = document.createElement('button');
      card.type = 'button';
      card.className = 'word-card';
      card.style.background = color.bg;
      card.style.color = color.fg;
      card.dataset.word = word;
      card.setAttribute('aria-pressed', 'false');
      card.setAttribute('aria-expanded', 'false');

      const headerEl = document.createElement('div');
      headerEl.className = 'word-card-header';

      const nameEl = document.createElement('span');
      nameEl.className = 'word-name';
      nameEl.textContent = word;

      const chevronEl = document.createElement('span');
      chevronEl.className = 'word-chevron';
      chevronEl.setAttribute('aria-hidden', 'true');
      chevronEl.textContent = '▸';

      headerEl.append(nameEl, chevronEl);

      const dirsEl = document.createElement('div');
      dirsEl.className = 'word-directions';
      const dirSteps = computeWordDirections(p.positions);
      const last = dirSteps.length - 1;
      dirsEl.dataset.labeled = dirSteps
        .map((s, idx) => (idx === last ? `Finish: ${s}` : `${idx + 1}. ${word[idx]}: ${s}`))
        .join('\n');
      dirsEl.dataset.unlabeled = dirSteps
        .map((s, idx) => (idx === last ? `Finish: ${s}` : `${idx + 1}. ${s}`))
        .join('\n');
      dirsEl.textContent = dotsMode ? dirsEl.dataset.unlabeled : dirsEl.dataset.labeled;

      card.append(headerEl, dirsEl);
      card.addEventListener('click', () => toggleWordHighlight(word, card));
      container.appendChild(card);
    });
  }

  /**
   * Single source of truth for live SVG drawing:
   * - Static wall segments between walled tile pairs.
   * - In dots mode: dark grey dots for all 25 cells, plus red control rings around
   *   the selected word's cells.
   * - When a word is selected: step numbers (centered white in dots mode,
   *   top-right badge in letter mode).
   */
  function redrawSVG() {
    const svg = document.getElementById('word-path');
    if (!svg) return;
    svg.innerHTML = '';
    if (!currentResult) return;

    const svgRect = svg.getBoundingClientRect();
    if (svgRect.width === 0 || svgRect.height === 0) return;

    const centerOf = el => {
      const r = el.getBoundingClientRect();
      return { x: r.left + r.width / 2 - svgRect.left, y: r.top + r.height / 2 - svgRect.top };
    };

    // Cache all cell centers once for this redraw
    const cellCenters = Array.from({ length: GRID_SIZE }, (_, r) =>
      Array.from({ length: GRID_SIZE }, (_, c) => centerOf(document.getElementById(`cell-${r}-${c}`)))
    );
    const sampleCell = document.getElementById('cell-0-0');
    const cellVisualRadius = sampleCell ? sampleCell.getBoundingClientRect().width / 2 : 21;

    // Draw static walls between walled tile pairs, offset by half stroke width so
    // round linecaps terminate cleanly at the circle perimeter without poking inside.
    const WALL_STROKE = 6;
    const wallR = (dotsMode ? 10 : cellVisualRadius) + WALL_STROKE / 2;
    for (const [t1, t2] of WALLS) {
      const [r1, c1] = tileToRC(t1);
      const [r2, c2] = tileToRC(t2);
      const p1 = cellCenters[r1][c1];
      const p2 = cellCenters[r2][c2];
      const dx = p2.x - p1.x;
      const dy = p2.y - p1.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist <= wallR * 2) continue;
      const ux = dx / dist;
      const uy = dy / dist;
      const wall = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      wall.setAttribute('x1', (p1.x + ux * wallR).toFixed(1));
      wall.setAttribute('y1', (p1.y + uy * wallR).toFixed(1));
      wall.setAttribute('x2', (p2.x - ux * wallR).toFixed(1));
      wall.setAttribute('y2', (p2.y - uy * wallR).toFixed(1));
      wall.setAttribute('stroke', '#1e293b');
      wall.setAttribute('stroke-width', String(WALL_STROKE));
      wall.setAttribute('stroke-linecap', 'round');
      svg.appendChild(wall);
    }

    if (dotsMode) {
      const wordCells = selectedWord
        ? new Set(currentResult.placements[selectedWord].positions.map(([r, c]) => `${r},${c}`))
        : null;

      for (let r = 0; r < GRID_SIZE; r++) {
        for (let c = 0; c < GRID_SIZE; c++) {
          const p = cellCenters[r][c];
          const isWordCell = wordCells && wordCells.has(`${r},${c}`);
          const circle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
          circle.setAttribute('cx', p.x.toFixed(1));
          circle.setAttribute('cy', p.y.toFixed(1));
          circle.setAttribute('r', '10');
          circle.setAttribute('fill', '#4b5563');
          svg.appendChild(circle);

          if (isWordCell) {
            const ring = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
            ring.setAttribute('cx', p.x.toFixed(1));
            ring.setAttribute('cy', p.y.toFixed(1));
            ring.setAttribute('r', '15');
            ring.setAttribute('fill', 'none');
            ring.setAttribute('stroke', PATH_COLOR);
            ring.setAttribute('stroke-width', '2.5');
            svg.appendChild(ring);
          }
        }
      }
    }

    if (!selectedWord) return;

    const positions = currentResult.placements[selectedWord].positions;

    // Draw step numbers: centered on dark dot in dots mode; top-right badge in letter mode.
    const wordIdx = currentResult.orderedWords.indexOf(selectedWord);
    const fgColor = PALETTE[wordIdx % PALETTE.length].fg;
    positions.forEach(([r, c], i) => {
      const p = cellCenters[r][c];
      if (dotsMode) {
        const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        txt.setAttribute('x', p.x.toFixed(1));
        txt.setAttribute('y', p.y.toFixed(1));
        txt.setAttribute('text-anchor', 'middle');
        txt.setAttribute('dominant-baseline', 'central');
        txt.setAttribute('font-family', 'sans-serif');
        txt.setAttribute('font-weight', '700');
        txt.setAttribute('font-size', '11');
        txt.setAttribute('fill', '#ffffff');
        txt.textContent = String(i + 1);
        svg.appendChild(txt);
      } else {
        const bx = p.x + cellVisualRadius * 0.72;
        const by = p.y - cellVisualRadius * 0.72;
        const badge = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        badge.setAttribute('cx', bx.toFixed(1));
        badge.setAttribute('cy', by.toFixed(1));
        badge.setAttribute('r', '8.5');
        badge.setAttribute('fill', fgColor);
        badge.setAttribute('stroke', '#ffffff');
        badge.setAttribute('stroke-width', '1.5');
        svg.appendChild(badge);

        const txt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        txt.setAttribute('x', bx.toFixed(1));
        txt.setAttribute('y', by.toFixed(1));
        txt.setAttribute('text-anchor', 'middle');
        txt.setAttribute('dominant-baseline', 'central');
        txt.setAttribute('font-family', 'sans-serif');
        txt.setAttribute('font-weight', '700');
        txt.setAttribute('font-size', '9.5');
        txt.setAttribute('fill', '#ffffff');
        txt.textContent = String(i + 1);
        svg.appendChild(txt);
      }
    });
  }

  function toggleWordHighlight(word, cardEl) {
    const cards = document.querySelectorAll('.word-card');
    if (selectedWord === word) {
      selectedWord = null;
      cards.forEach(c => {
        c.classList.remove('selected');
        c.setAttribute('aria-pressed', 'false');
        c.setAttribute('aria-expanded', 'false');
      });
    } else {
      selectedWord = word;
      cards.forEach(c => {
        c.classList.remove('selected');
        c.setAttribute('aria-pressed', 'false');
        c.setAttribute('aria-expanded', 'false');
      });
      cardEl.classList.add('selected');
      cardEl.setAttribute('aria-pressed', 'true');
      cardEl.setAttribute('aria-expanded', 'true');
    }
    applyDotsMode();
  }

  // ── Print mode ─────────────────────────────────────────────────────────────────

  let openPrintUrls = [];

  function buildPrintHTML(result) {
    const { grid, placements, orderedWords } = result;

    // SVG layout constants: 6 columns (5 grid + End) x 6 rows (5 grid + Start)
    const PC = 56;
    const PG = 8;
    const PS = PC + PG;
    const PR = Math.round(PC * 0.36); // ~20px circle radius
    const PAD = 24;
    const SVG_W = 5 * PS + PC + PAD * 2;      // 424px
    const SVG_H = 5 * PS + PC + PAD * 2 + 12; // 436px (extra room for START label)

    function cc(r, c) {
      return { x: PAD + c * PS + PC / 2, y: PAD + r * PS + PC / 2 };
    }
    const CS = { x: PAD + 2 * PS + PC / 2, y: PAD + 5 * PS + PC / 2 };
    const CE = { x: PAD + 5 * PS + PC / 2, y: PAD + 2 * PS + PC / 2 };

    function svgWalls(baseR) {
      const wallStroke = 5;
      const wallR = baseR + wallStroke / 2;
      return WALLS.map(([t1, t2]) => {
        const [r1, c1] = tileToRC(t1);
        const [r2, c2] = tileToRC(t2);
        const p1 = cc(r1, c1);
        const p2 = cc(r2, c2);
        const dx = p2.x - p1.x;
        const dy = p2.y - p1.y;
        const d = Math.sqrt(dx * dx + dy * dy);
        if (d <= wallR * 2) return '';
        const ux = dx / d;
        const uy = dy / d;
        return `<line x1="${(p1.x + ux * wallR).toFixed(1)}" y1="${(p1.y + uy * wallR).toFixed(1)}" x2="${(p2.x - ux * wallR).toFixed(1)}" y2="${(p2.y - uy * wallR).toFixed(1)}" stroke="#1e293b" stroke-width="${wallStroke}" stroke-linecap="round"/>`;
      }).join('');
    }

    function svgCells(showLetters, activeSet) {
      let s = '';
      for (let r = 0; r < GRID_SIZE; r++) {
        for (let c = 0; c < GRID_SIZE; c++) {
          const p = cc(r, c);
          const active = activeSet && activeSet.has(`${r},${c}`);
          if (showLetters) {
            s += `<circle cx="${p.x}" cy="${p.y}" r="${PR}" fill="#f8fafc" stroke="#64748b" stroke-width="1.5"/>`;
            s += `<text x="${p.x}" y="${p.y}" text-anchor="middle" dominant-baseline="central" font-family="Menlo,Consolas,monospace" font-weight="800" font-size="18" fill="#0f172a">${escapeHtml(grid[r][c])}</text>`;
          } else {
            s += `<circle cx="${p.x}" cy="${p.y}" r="${active ? 11.5 : 10}" fill="#1e293b"/>`;
            if (active) {
              s += `<circle cx="${p.x}" cy="${p.y}" r="16" fill="none" stroke="${PATH_COLOR}" stroke-width="2.5"/>`;
            }
          }
        }
      }
      return s;
    }

    function svgNumbers(stepMap) {
      if (!stepMap) return '';
      let s = '';
      stepMap.forEach((num, key) => {
        const [r, c] = key.split(',').map(Number);
        const p = cc(r, c);
        s += `<text x="${p.x}" y="${p.y}" text-anchor="middle" dominant-baseline="central" font-family="sans-serif" font-weight="800" font-size="13" fill="#ffffff">${num}</text>`;
      });
      return s;
    }

    function svgMarkers() {
      return [
        // Start marker (triangle) + label below circle
        `<circle cx="${CS.x}" cy="${CS.y}" r="${PR}" fill="#f8fafc" stroke="#475569" stroke-width="1.5"/>`,
        `<polygon points="${CS.x},${CS.y - 7} ${CS.x + 7},${CS.y + 6} ${CS.x - 7},${CS.y + 6}" fill="#1e293b"/>`,
        `<text x="${CS.x}" y="${CS.y + PR + 11}" text-anchor="middle" font-family="sans-serif" font-weight="700" font-size="9" letter-spacing="0.06em" fill="#334155">START</text>`,
        // End marker (bullseye) + label below circle
        `<circle cx="${CE.x}" cy="${CE.y}" r="${PR}" fill="#f8fafc" stroke="#475569" stroke-width="1.5"/>`,
        `<circle cx="${CE.x}" cy="${CE.y}" r="8" fill="none" stroke="#1e293b" stroke-width="1.75"/>`,
        `<circle cx="${CE.x}" cy="${CE.y}" r="2.75" fill="#1e293b"/>`,
        `<text x="${CE.x}" y="${CE.y + PR + 11}" text-anchor="middle" font-family="sans-serif" font-weight="700" font-size="9" letter-spacing="0.06em" fill="#334155">END</text>`,
      ].join('');
    }

    function svgCompass() {
      // Positioned in the empty top-right corner of col 5 above the End marker
      const cx = PAD + 5 * PS + PC / 2;
      const cy = PAD + PC / 2 + 10;
      const R = 19;
      const arm = 12;
      const tip = 6;
      const labelOffset = R + 9;
      return [
        `<circle cx="${cx}" cy="${cy}" r="${R}" fill="#ffffff" stroke="#64748b" stroke-width="1.5"/>`,
        `<polygon points="${cx},${cy - arm} ${cx - tip / 2},${cy} ${cx + tip / 2},${cy}" fill="#0f172a"/>`,
        `<polygon points="${cx},${cy + arm} ${cx - tip / 2},${cy} ${cx + tip / 2},${cy}" fill="#e2e8f0" stroke="#475569" stroke-width="0.75"/>`,
        `<line x1="${cx - arm}" y1="${cy}" x2="${cx + arm}" y2="${cy}" stroke="#475569" stroke-width="1.5"/>`,
        `<text x="${cx}" y="${cy - labelOffset}" text-anchor="middle" dominant-baseline="central" font-family="sans-serif" font-weight="800" font-size="10" fill="#0f172a">N</text>`,
        `<text x="${cx}" y="${cy + labelOffset}" text-anchor="middle" dominant-baseline="central" font-family="sans-serif" font-weight="600" font-size="9" fill="#334155">S</text>`,
        `<text x="${cx + labelOffset}" y="${cy}" text-anchor="middle" dominant-baseline="central" font-family="sans-serif" font-weight="600" font-size="9" fill="#334155">E</text>`,
        `<text x="${cx - labelOffset}" y="${cy}" text-anchor="middle" dominant-baseline="central" font-family="sans-serif" font-weight="600" font-size="9" fill="#334155">W</text>`,
      ].join('');
    }

    function buildSVG(showLetters, activePositions, ariaLabel, maxWidth = 440) {
      const activeSet = activePositions ? new Set(activePositions.map(([r, c]) => `${r},${c}`)) : null;
      const stepMap = (!showLetters && activePositions)
        ? new Map(activePositions.map(([r, c], i) => [`${r},${c}`, i + 1]))
        : null;
      // Draw walls first with baseR = 17.5 in dots mode so walls never touch r = 16 control rings
      return `<svg role="img" aria-label="${escapeHtml(ariaLabel)}" viewBox="0 0 ${SVG_W} ${SVG_H}" width="${SVG_W}" height="${SVG_H}" style="width:100%;max-width:${maxWidth}px;height:auto;display:block;margin:0 auto">` +
        svgWalls(showLetters ? PR : 17.5) +
        svgCells(showLetters, activeSet) +
        svgMarkers() +
        svgCompass() +
        svgNumbers(stepMap) +
        `</svg>`;
    }

    function buildLetterBoxes(length) {
      return Array.from({ length }, (_, j) =>
        `<div class="letter-box"><div class="letter-box-square"></div><div class="letter-box-num">${j + 1}</div></div>`
      ).join('');
    }

    function buildLetterCardPage(cellsHtml) {
      return `<section class="lc-page section-cards" aria-label="Printable sign cards">` +
        `<div class="lc-col">${cellsHtml}</div>` +
        `<div class="lc-fold"></div>` +
        `<div class="lc-col">${cellsHtml}</div>` +
        `<div class="lc-hcut" style="top:33.333%"></div>` +
        `<div class="lc-hcut" style="top:66.667%"></div>` +
        `</section>`;
    }

    // Combine 2 marker cards + 25 letter cards = 27 cards -> 9 full pages (0 blank slots)
    const startSvg = `<svg width="165" height="165" viewBox="0 0 14 14" aria-hidden="true"><polygon points="7,1.5 13,12.5 1,12.5" fill="#0f172a"/></svg>`;
    const endSvg = `<svg width="165" height="165" viewBox="0 0 14 14" aria-hidden="true"><circle cx="7" cy="7" r="5.5" fill="none" stroke="#0f172a" stroke-width="1.4"/><circle cx="7" cy="7" r="2" fill="#0f172a"/></svg>`;
    const allCardCells = [
      `<div class="lc-cell-marker">${startSvg}<div class="lc-marker-label">Start</div></div>`,
      `<div class="lc-cell-marker">${endSvg}<div class="lc-marker-label">End</div></div>`,
      ...grid.flat().slice().sort().map(ch =>
        `<div class="lc-cell"><span>${escapeHtml(ch)}</span><span class="lc-underline"></span></div>`
      ),
    ];
    const cardPageCount = Math.ceil(allCardCells.length / 3);
    const totalInitialPages = 1 + orderedWords.length * 2 + cardPageCount;

    const css = `
      *{box-sizing:border-box;margin:0;padding:0}
      body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#0f172a;background:#f1f5f9;print-color-adjust:exact;-webkit-print-color-adjust:exact}
      .toolbar{position:sticky;top:0;z-index:10;background:#ffffff;border-bottom:1px solid #cbd5e1;padding:.85rem 1.5rem;display:flex;align-items:center;justify-content:space-between;gap:.85rem 1.25rem;flex-wrap:wrap;box-shadow:0 1px 3px rgba(0,0,0,.06)}
      .toolbar-title{font-size:1rem;font-weight:800;color:#0f172a}
      .toolbar-controls{display:flex;align-items:center;gap:.35rem 1rem;flex-wrap:wrap;font-size:.875rem;color:#334155}
      .toolbar-controls label{display:inline-flex;align-items:center;gap:.4rem;cursor:pointer;min-height:38px;padding:.15rem .25rem;border-radius:6px}
      .toolbar-controls input:focus-visible{outline:2px solid #2563eb;outline-offset:2px}
      .toolbar-note{width:100%;font-size:.78rem;color:#475569}
      .print-action{padding:.55rem 1.25rem;background:#2563eb;color:#fff;border:none;border-radius:7px;font-size:.9rem;font-weight:600;cursor:pointer;white-space:nowrap}
      .print-action:hover:not(:disabled){background:#1d4ed8}
      .print-action:focus-visible{outline:2px solid #2563eb;outline-offset:2px}
      .print-action:disabled{background:#94a3b8;cursor:not-allowed}
      .empty-state{display:none;max-width:520px;margin:4rem auto;padding:2rem;text-align:center;background:#ffffff;border:1px solid #cbd5e1;border-radius:12px;color:#334155;font-size:.95rem}
      .empty-state.visible{display:block}
      .page{background:#ffffff;max-width:8.5in;margin:1.25rem auto;padding:1.5rem 2rem;box-shadow:0 1px 4px rgba(0,0,0,.08);page-break-before:always;break-before:page}
      .sheet-head{display:flex;align-items:baseline;justify-content:space-between;gap:1rem;border-bottom:2px solid #cbd5e1;padding-bottom:.45rem;margin-bottom:.65rem}
      .sheet-head h2{font-size:1.25rem;font-weight:800;color:#0f172a}
      .sheet-meta{display:flex;align-items:baseline;gap:1.25rem;font-size:.85rem;color:#334155}
      .badge{font-weight:700;color:#334155}
      .name-field{white-space:nowrap;font-size:.82rem;color:#475569}
      .name-line{display:inline-block;width:9rem;border-bottom:1.5px solid #64748b;margin-left:.3rem}
      .sheet-instructions{font-size:.82rem;color:#334155;line-height:1.45;margin-bottom:1rem}
      .key-label{font-size:.78rem;font-weight:700;text-transform:uppercase;letter-spacing:.07em;color:#334155}
      .coord-words{display:flex;gap:.75rem;flex-wrap:wrap;justify-content:center;margin-top:1.15rem}
      .coord-pill{font-family:Menlo,Consolas,monospace;font-size:1rem;font-weight:800;letter-spacing:.08em;color:#0f172a;background:#f1f5f9;border:1.5px solid #94a3b8;border-radius:7px;padding:.35rem .75rem}
      .coord-pill-num{color:#475569;font-weight:700;margin-right:.35rem}
      .runner-page{display:flex;flex-direction:column;align-items:center}
      .hard-layout{display:flex;gap:1.5rem;align-items:flex-start;justify-content:center;width:100%;flex-wrap:wrap}
      .hard-steps-col{min-width:205px;max-width:270px}
      .steps{list-style:none;font-family:Menlo,Consolas,monospace;font-size:.88rem;color:#0f172a;margin-top:.45rem}
      .step{display:flex;align-items:baseline;gap:.45rem;padding:.34rem 0;border-bottom:1px solid #e2e8f0}
      .step-check{display:inline-block;width:.85rem;height:.85rem;border:1.5px solid #475569;border-radius:2px;flex-shrink:0;transform:translateY(1px)}
      .step-idx{font-weight:800;color:#334155;min-width:1.4rem}
      .letter-boxes{display:flex;gap:.55rem;flex-wrap:wrap;margin-top:1.25rem;justify-content:center}
      .letter-box{display:flex;flex-direction:column;align-items:center;gap:.25rem}
      .letter-box-square{width:3rem;height:3rem;border:2px solid #334155;border-radius:4px}
      .letter-box-num{font-size:.72rem;font-weight:700;color:#334155;font-family:sans-serif}
      .lc-page{background:#ffffff;max-width:8.5in;height:10.5in;margin:1.25rem auto;padding:0!important;display:flex;position:relative;box-shadow:0 1px 4px rgba(0,0,0,.08);page-break-before:always;break-before:page;break-inside:avoid;overflow:hidden}
      .lc-col{flex:1;display:flex;flex-direction:column}
      .lc-cell{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center;font-family:Menlo,Consolas,monospace;font-weight:900;font-size:2.7in;line-height:1;color:#0f172a}
      .lc-underline{width:1.4in;height:6px;background:#334155;border-radius:3px;margin-top:.08in}
      .lc-cell-marker{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:center}
      .lc-marker-label{font-family:sans-serif;font-size:.42in;font-weight:700;letter-spacing:.1em;text-transform:uppercase;color:#1e293b;margin-top:.12in}
      .lc-fold{position:absolute;left:50%;top:0;bottom:0;border-left:2px dashed #64748b;pointer-events:none}
      .lc-hcut{position:absolute;left:0;right:0;height:0;border-top:1px dashed #94a3b8;pointer-events:none}
      .lc-hcut::before{content:'✂';position:absolute;left:.35in;top:-.55em;font-size:14px;color:#334155}
      .first-visible{page-break-before:auto!important;break-before:auto!important}
      .hidden-section{display:none!important}
      @media print{
        body{background:#ffffff}
        .no-print{display:none!important}
        .page{max-width:none;margin:0;padding:.85cm 1.4cm;box-shadow:none}
        .lc-page{max-width:none;margin:0;height:10.75in;box-shadow:none}
        @page{margin:0}
      }
    `;

    let html = `<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>Maze-O Generator — Print Sheets</title><style>${css}</style></head><body>`;

    // Non-printing interactive toolbar
    html += `<header class="toolbar no-print">` +
      `<h1 class="toolbar-title">Maze-O Print Sheets</h1>` +
      `<div class="toolbar-controls" role="group" aria-label="Sections to include">` +
      `<label><input type="checkbox" checked data-section="section-coord"> Coordinator (1)</label>` +
      `<label><input type="checkbox" checked data-section="section-easy"> Easy Runner (${orderedWords.length})</label>` +
      `<label><input type="checkbox" checked data-section="section-hard"> Hard Runner (${orderedWords.length})</label>` +
      `<label><input type="checkbox" checked data-section="section-cards"> Sign &amp; Letter Cards (${cardPageCount})</label>` +
      `</div>` +
      `<button type="button" id="print-sheets-btn" class="print-action" onclick="window.print()">Print ${totalInitialPages} Sheets</button>` +
      `<p class="toolbar-note">Sign &amp; Letter Cards: cut along horizontal dashed lines and fold along the vertical center line to make standing signs.</p>` +
      `</header>`;

    html += `<div id="empty-state" class="empty-state no-print" role="status" aria-live="polite">No sections selected. Check at least one section above to preview and print.</div>`;
    html += `<main id="sheets">`;

    // 1. Maze Coordinator
    html += `<section class="page section-coord" aria-label="Maze Coordinator Answer Key">` +
      `<div class="sheet-head"><h2>Maze Coordinator</h2><span class="badge">Answer Key</span></div>` +
      `<p class="sheet-instructions">Place the Start (▲), End (⊙), walls, and letter signs to match the grid below. Use the word list to verify runner answers.</p>` +
      `<div class="runner-page">${buildSVG(true, null, 'Maze Coordinator 5 by 5 letter grid with walls, Start, End, and compass', 460)}<div class="coord-words">`;
    orderedWords.forEach((word, i) => {
      html += `<div class="coord-pill"><span class="coord-pill-num">#${i + 1}</span>${escapeHtml(word)}</div>`;
    });
    html += `</div></div></section>`;

    // 2. Maze Runner – Easy (one per word)
    orderedWords.forEach((word, i) => {
      html += `<section class="page section-easy" aria-label="Maze Runner Easy sheet ${i + 1} of ${orderedWords.length}">` +
        `<div class="sheet-head"><h2>Maze Runner &ndash; Easy</h2><div class="sheet-meta"><span class="name-field">Name:<span class="name-line"></span></span><span class="badge">#${i + 1} of ${orderedWords.length}</span></div></div>` +
        `<p class="sheet-instructions">Start at ▲. Visit each numbered circle in order without crossing walls, write the letter you find in the matching box below, then finish at ⊙.</p>` +
        `<div class="runner-page">` +
        buildSVG(false, placements[word].positions, `Maze Runner Easy map #${i + 1} with numbered checkpoints`, 440) +
        `<div class="letter-boxes">${buildLetterBoxes(word.length)}</div>` +
        `</div></section>`;
    });

    // 3. Maze Runner – Hard (one per word)
    orderedWords.forEach((word, i) => {
      const dirs = computeWordDirections(placements[word].positions);
      html += `<section class="page section-hard" aria-label="Maze Runner Hard sheet ${i + 1} of ${orderedWords.length}">` +
        `<div class="sheet-head"><h2>Maze Runner &ndash; Hard</h2><div class="sheet-meta"><span class="name-field">Name:<span class="name-line"></span></span><span class="badge">#${i + 1} of ${orderedWords.length}</span></div></div>` +
        `<p class="sheet-instructions">Start at ▲ and follow each compass step (1 step = 1 dot; do not cross walls). Write the letter at each numbered stop below, then follow Finish to ⊙.</p>` +
        `<div class="runner-page">` +
        `<div class="hard-layout">` +
        `<div style="flex:1;min-width:250px">${buildSVG(false, null, `Maze Runner Hard blank grid #${i + 1} with walls and compass`, 360)}</div>` +
        `<div class="hard-steps-col">` +
        `<div class="key-label">Directions</div>` +
        `<ol class="steps">${dirs.map((s, j) => (j === dirs.length - 1
          ? `<li class="step"><span class="step-check" aria-hidden="true"></span><span><strong>Finish:</strong> ${escapeHtml(s)}</span></li>`
          : `<li class="step"><span class="step-check" aria-hidden="true"></span><span class="step-idx">${j + 1}.</span><span>${escapeHtml(s)}</span></li>`)).join('')}</ol>` +
        `</div>` +
        `</div>` +
        `<div class="letter-boxes">${buildLetterBoxes(word.length)}</div>` +
        `</div></section>`;
    });

    // 4. Sign & Letter Cards (2 markers + 25 sorted letters = 27 cards -> 9 full pages)
    for (let i = 0; i < allCardCells.length; i += 3) {
      const group = allCardCells.slice(i, i + 3);
      while (group.length < 3) group.push('<div class="lc-cell"></div>');
      html += buildLetterCardPage(group.join(''));
    }

    html += `</main><script>
      (function () {
        const checkboxes = document.querySelectorAll('.toolbar input[data-section]');
        const printBtn = document.getElementById('print-sheets-btn');
        const emptyState = document.getElementById('empty-state');

        function syncSheets() {
          checkboxes.forEach(cb => {
            document.querySelectorAll('.' + cb.dataset.section).forEach(el => {
              el.classList.toggle('hidden-section', !cb.checked);
            });
          });
          const allSheets = Array.from(document.querySelectorAll('#sheets > section'));
          allSheets.forEach(el => el.classList.remove('first-visible'));
          const visible = allSheets.filter(el => !el.classList.contains('hidden-section'));
          if (visible.length > 0) visible[0].classList.add('first-visible');

          printBtn.disabled = visible.length === 0;
          printBtn.textContent = visible.length === 0
            ? 'No Sheets Selected'
            : 'Print ' + visible.length + (visible.length === 1 ? ' Sheet' : ' Sheets');
          emptyState.classList.toggle('visible', visible.length === 0);
        }

        checkboxes.forEach(cb => cb.addEventListener('change', syncSheets));
        syncSheets();
      })();
    <\/script></body></html>`;
    return html;
  }

  function openPrintWindow() {
    if (!currentResult) return;
    const html = buildPrintHTML(currentResult);
    const blob = new Blob([html], { type: 'text/html' });
    const url = URL.createObjectURL(blob);
    const w = window.open(url, '_blank');
    if (!w) {
      URL.revokeObjectURL(url);
      showError('Pop-up blocked. Please allow pop-ups for this site to open the printable sheets.', { markInputInvalid: false });
      return;
    }
    openPrintUrls.push(url);
  }

  // ── Shareable URL state & local history ───────────────────────────────────────

  const HISTORY_STORAGE_KEY = 'mazeo_history_v1';
  const MAX_HISTORY = 10;
  let currentMazeCode = '';

  /**
   * Encode a generated maze result into a compact URL-safe string:
   * 25 grid letters (A-Z) + "." + comma-separated base-36 cell indices (0-9a-o) per word.
   */
  function encodeMazeState(result) {
    const gridStr = result.grid.flat().join('');
    const wordCodes = result.orderedWords.map(word =>
      result.placements[word].positions
        .map(([r, c]) => (r * GRID_SIZE + c).toString(36))
        .join('')
    );
    return `${gridStr}.${wordCodes.join(',')}`;
  }

  /**
   * Decode a compact maze code (or "#m=..." hash) back into { grid, placements, orderedWords },
   * returning null if malformed.
   */
  function decodeMazeState(rawCode) {
    if (typeof rawCode !== 'string') return null;
    const cleaned = rawCode.trim().replace(/^#/, '').replace(/^m=/, '');
    const match = cleaned.match(/^([A-Z]{25})\.([0-9a-o]{1,8}(?:,[0-9a-o]{1,8}){0,3})$/);
    if (!match) return null;

    const [, gridStr, wordsStr] = match;
    const grid = [];
    for (let r = 0; r < GRID_SIZE; r++) {
      grid.push(gridStr.slice(r * GRID_SIZE, (r + 1) * GRID_SIZE).split(''));
    }

    const orderedWords = [];
    const placements = {};
    for (const posStr of wordsStr.split(',')) {
      const seen = new Set();
      const positions = [];
      let word = '';
      for (const ch of posStr) {
        const idx = parseInt(ch, 36);
        if (Number.isNaN(idx) || idx < 0 || idx >= GRID_CELLS || seen.has(idx)) return null;
        seen.add(idx);
        const r = Math.floor(idx / GRID_SIZE);
        const c = idx % GRID_SIZE;
        positions.push([r, c]);
        word += grid[r][c];
      }
      if (placements[word]) return null;
      orderedWords.push(word);
      placements[word] = { positions };
    }

    return { grid, placements, orderedWords };
  }

  function loadHistory() {
    try {
      const raw = window.localStorage.getItem(HISTORY_STORAGE_KEY);
      if (!raw) return [];
      const parsed = JSON.parse(raw);
      if (!Array.isArray(parsed)) return [];
      return parsed.filter(item =>
        item && typeof item.code === 'string' && decodeMazeState(item.code) !== null
      );
    } catch {
      return [];
    }
  }

  function saveHistory(entries) {
    try {
      window.localStorage.setItem(HISTORY_STORAGE_KEY, JSON.stringify(entries.slice(0, MAX_HISTORY)));
    } catch {
      // Ignore storage quota or private-mode errors
    }
  }

  function formatSavedDate(ts) {
    if (!ts) return '';
    try {
      return new Date(ts).toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
    } catch {
      return '';
    }
  }

  function renderHistory() {
    const card = document.getElementById('history-card');
    const list = document.getElementById('history-list');
    if (!card || !list) return;

    const entries = loadHistory();
    list.innerHTML = '';
    if (entries.length === 0) {
      card.classList.remove('visible');
      return;
    }

    card.classList.add('visible');
    entries.forEach(entry => {
      const li = document.createElement('li');
      li.className = 'history-item' + (entry.code === currentMazeCode ? ' active' : '');

      const loadBtn = document.createElement('button');
      loadBtn.type = 'button';
      loadBtn.className = 'history-load-btn';
      const wordsLabel = Array.isArray(entry.words) ? entry.words.join(' · ') : '';

      const wordsSpan = document.createElement('span');
      wordsSpan.className = 'history-words';
      wordsSpan.textContent = wordsLabel;

      const dateSpan = document.createElement('span');
      dateSpan.className = 'history-date';
      dateSpan.textContent = formatSavedDate(entry.savedAt);

      loadBtn.append(wordsSpan, dateSpan);
      loadBtn.addEventListener('click', () => {
        restoreFromCode(entry.code, { record: false, scroll: true });
      });

      const removeBtn = document.createElement('button');
      removeBtn.type = 'button';
      removeBtn.className = 'history-remove-btn';
      removeBtn.setAttribute('aria-label', `Remove ${wordsLabel} from recent mazes`);
      removeBtn.textContent = '×';
      removeBtn.addEventListener('click', () => {
        const next = loadHistory().filter(item => item.code !== entry.code);
        saveHistory(next);
        renderHistory();
      });

      li.append(loadBtn, removeBtn);
      list.appendChild(li);
    });
  }

  function recordHistory(result, code) {
    const entries = loadHistory().filter(item => item.code !== code);
    entries.unshift({
      code,
      words: result.orderedWords,
      savedAt: Date.now(),
    });
    saveHistory(entries);
    renderHistory();
  }

  function syncUrlHash(code) {
    currentMazeCode = code;
    try {
      const target = `#m=${code}`;
      if (window.location.hash !== target) {
        window.history.replaceState(null, '', target);
      }
    } catch {
      // Ignore history API restrictions
    }
  }

  function showMazeResult(result, rawText, { record = true, scroll = true } = {}) {
    lastGeneratedRaw = rawText;
    const code = encodeMazeState(result);
    syncUrlHash(code);

    const output = document.getElementById('output');
    const wasHidden = !output.classList.contains('visible');
    output.classList.add('visible');
    renderAll(result);
    document.getElementById('generate-btn').textContent = 'Regenerate Maze';

    if (record) {
      recordHistory(result, code);
    } else {
      renderHistory();
    }

    if (scroll) {
      const rect = output.getBoundingClientRect();
      const isVisible = rect.top >= 0 && rect.top < window.innerHeight * 0.75;
      if (wasHidden || !isVisible) {
        const reduceMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
        output.scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'start' });
      }
    }
  }

  function restoreFromCode(code, { record = false, scroll = false } = {}) {
    const result = decodeMazeState(code);
    if (!result) return false;
    clearError();
    clearNotice();
    const rawText = result.orderedWords.join('\n');
    wordsInput.value = rawText;
    showMazeResult(result, rawText, { record, scroll });
    updateInputMeta();
    return true;
  }

  let copyResetTimer = null;
  function copyShareLink() {
    if (!currentResult || !currentMazeCode) return;
    syncUrlHash(currentMazeCode);
    const url = window.location.href;
    const btn = document.getElementById('copy-link-btn');

    const onCopied = () => {
      btn.textContent = 'Link Copied!';
      clearTimeout(copyResetTimer);
      copyResetTimer = setTimeout(() => {
        btn.textContent = 'Copy Link';
      }, 2000);
    };

    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(url).then(onCopied).catch(() => {
        showNotice(`Share link: ${url}`);
      });
    } else {
      const tmp = document.createElement('textarea');
      tmp.value = url;
      tmp.setAttribute('readonly', '');
      tmp.style.position = 'fixed';
      tmp.style.opacity = '0';
      document.body.appendChild(tmp);
      tmp.select();
      try {
        document.execCommand('copy');
        onCopied();
      } catch {
        showNotice(`Share link: ${url}`);
      }
      document.body.removeChild(tmp);
    }
  }

  // ── Input parsing ──────────────────────────────────────────────────────────────

  function parseInput(raw) {
    const rawLines = raw.split('\n').map(l => l.trim()).filter(l => l.length > 0);
    let strippedChars = false;
    const cleaned = [];
    for (const line of rawLines) {
      const upper = line.toUpperCase();
      const lettersOnly = upper.replace(/[^A-Z]/g, '');
      if (lettersOnly !== upper) strippedChars = true;
      if (lettersOnly.length > 0) cleaned.push(lettersOnly);
    }
    const unique = [...new Set(cleaned)];
    const removedDuplicates = cleaned.length - unique.length;
    return { words: unique, strippedChars, removedDuplicates };
  }

  // ── DOM wiring (browser only) ──────────────────────────────────────────────────

  let wordsInput;
  let errorEl;
  let noticeEl;
  let inputMetaEl;
  let staleBannerEl;

  function showError(msg, { markInputInvalid = true } = {}) {
    if (!errorEl) return;
    errorEl.textContent = msg;
    errorEl.style.display = 'block';
    if (wordsInput) {
      if (markInputInvalid) {
        wordsInput.setAttribute('aria-invalid', 'true');
      } else {
        wordsInput.removeAttribute('aria-invalid');
      }
    }
  }

  function clearError() {
    if (!errorEl) return;
    errorEl.style.display = 'none';
    errorEl.textContent = '';
    if (wordsInput) wordsInput.removeAttribute('aria-invalid');
  }

  function showNotice(msg) {
    if (!noticeEl) return;
    noticeEl.textContent = msg;
    noticeEl.classList.add('visible');
  }

  function clearNotice() {
    if (!noticeEl) return;
    noticeEl.textContent = '';
    noticeEl.classList.remove('visible');
  }

  function updateInputMeta() {
    const { words } = parseInput(wordsInput.value);
    const required = computeRequired(words);
    const totalRequired = Object.values(required).reduce((s, v) => s + v, 0);
    const cellText = words.length > 0 ? ` · ${totalRequired}/${GRID_CELLS} cells` : '';
    inputMetaEl.textContent = `${words.length}/${MAX_WORDS} words${cellText} · Ctrl/⌘+Enter to generate`;

    if (currentResult && wordsInput.value !== lastGeneratedRaw) {
      staleBannerEl.classList.add('visible');
    } else {
      staleBannerEl.classList.remove('visible');
    }
  }

  function handleGenerate() {
    clearError();
    clearNotice();

    const raw = wordsInput.value;
    const { words, strippedChars, removedDuplicates } = parseInput(raw);

    if (words.length === 0) {
      showError('Please enter at least one word (A–Z letters).');
      wordsInput.focus();
      return;
    }

    if (words.length > MAX_WORDS) {
      showError(`Please enter ${MAX_WORDS} words or fewer (currently ${words.length}).`);
      wordsInput.focus();
      return;
    }

    const tooLong = words.filter(w => w.length > MAX_WORD_LENGTH);
    if (tooLong.length > 0) {
      const list = tooLong.map(w => `"${w}" (${w.length} letters)`).join(', ');
      showError(`Words must be ${MAX_WORD_LENGTH} letters or fewer: ${list}.`);
      wordsInput.focus();
      return;
    }

    const result = generate(words);
    if (result.error) {
      showError(result.error);
      wordsInput.focus();
      return;
    }

    const notices = [];
    if (strippedChars) notices.push('non-letter characters were removed');
    if (removedDuplicates > 0) {
      notices.push(`${removedDuplicates} duplicate ${removedDuplicates === 1 ? 'word was' : 'words were'} skipped`);
    }
    if (notices.length > 0) {
      showNotice(`Note: ${notices.join(' and ')}.`);
    }

    showMazeResult(result, raw, { record: true, scroll: true });
  }

  if (typeof document !== 'undefined') {
    wordsInput = document.getElementById('words-input');
    errorEl = document.getElementById('error-msg');
    noticeEl = document.getElementById('input-notice');
    inputMetaEl = document.getElementById('input-meta');
    staleBannerEl = document.getElementById('stale-banner');

    window.addEventListener('beforeunload', () => {
      openPrintUrls.forEach(url => URL.revokeObjectURL(url));
      openPrintUrls = [];
    });

    window.addEventListener('beforeprint', () => {
      if (currentResult) redrawSVG();
    });

    document.getElementById('copy-link-btn').addEventListener('click', copyShareLink);
    document.getElementById('print-btn').addEventListener('click', openPrintWindow);
    document.getElementById('generate-btn').addEventListener('click', handleGenerate);

    document.getElementById('clear-history-btn').addEventListener('click', () => {
      saveHistory([]);
      renderHistory();
    });

    document.getElementById('example-btn').addEventListener('click', () => {
      wordsInput.value = 'HELPFUL\nTHRIFTY\nBRAVE';
      updateInputMeta();
      handleGenerate();
    });

    wordsInput.addEventListener('input', updateInputMeta);

    wordsInput.addEventListener('keydown', e => {
      if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
        e.preventDefault();
        handleGenerate();
      }
    });

    document.getElementById('dots-toggle').addEventListener('change', e => {
      dotsMode = e.target.checked;
      applyDotsMode();
    });

    // Keep live SVG aligned with CSS grid across viewport resizes / breakpoint changes
    const puzzleArea = document.querySelector('.puzzle-area');
    if (typeof ResizeObserver !== 'undefined' && puzzleArea) {
      new ResizeObserver(() => {
        if (currentResult) redrawSVG();
      }).observe(puzzleArea);
    } else {
      window.addEventListener('resize', () => {
        if (currentResult) redrawSVG();
      });
    }

    window.addEventListener('hashchange', () => {
      if (window.location.hash.startsWith('#m=')) {
        restoreFromCode(window.location.hash, { record: true, scroll: false });
      }
    });

    renderHistory();
    if (window.location.hash.startsWith('#m=')) {
      if (!restoreFromCode(window.location.hash, { record: true, scroll: false })) {
        showNotice('The shared maze link was invalid or incomplete.');
      }
    }
    updateInputMeta();
  }

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
      GRID_SIZE,
      GRID_CELLS,
      WALLS,
      START_POS,
      END_POS,
      BLOCKED_EDGES,
      tileToRC,
      escapeHtml,
      cross2d,
      onSegment,
      segmentsIntersect,
      computeRequired,
      buildCells,
      findNonCrossingPath,
      assignWords,
      generate,
      navBFS,
      compressSteps,
      computeWordDirections,
      parseInput,
      encodeMazeState,
      decodeMazeState,
      buildPrintHTML,
    };
  }
})();
