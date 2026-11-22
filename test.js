'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const {
  GRID_SIZE,
  GRID_CELLS,
  WALLS,
  START_POS,
  END_POS,
  BLOCKED_EDGES,
  tileToRC,
  escapeHtml,
  segmentsIntersect,
  computeRequired,
  findNonCrossingPath,
  generate,
  navBFS,
  compressSteps,
  computeWordDirections,
  parseInput,
  encodeMazeState,
  decodeMazeState,
  buildPrintHTML,
} = require('./script.js');

const DIR_DELTAS = {
  N: [-1, 0],
  S: [1, 0],
  E: [0, 1],
  W: [0, -1],
  NE: [-1, 1],
  SE: [1, 1],
  SW: [1, -1],
  NW: [-1, -1],
};

function traceSteps(r1, c1, steps) {
  let r = r1;
  let c = c1;
  const coords = [[r, c]];
  for (const dir of steps) {
    const [dr, dc] = DIR_DELTAS[dir];
    const nr = r + dr;
    const nc = c + dc;
    assert.equal(
      BLOCKED_EDGES.has(`${r},${c}|${nr},${nc}`),
      false,
      `Step (${r},${c}) -> (${nr},${nc}) crossed a blocked wall`
    );
    r = nr;
    c = nc;
    coords.push([r, c]);
  }
  return coords;
}

test('tileToRC maps 1-indexed tiles to 0-indexed row/col', () => {
  assert.deepEqual(tileToRC(1), [0, 0]);
  assert.deepEqual(tileToRC(5), [0, 4]);
  assert.deepEqual(tileToRC(6), [1, 0]);
  assert.deepEqual(tileToRC(13), [2, 2]);
  assert.deepEqual(tileToRC(25), [4, 4]);
});

test('BLOCKED_EDGES is symmetric for every wall pair', () => {
  assert.equal(BLOCKED_EDGES.size, WALLS.length * 2);
  for (const [t1, t2] of WALLS) {
    const [r1, c1] = tileToRC(t1);
    const [r2, c2] = tileToRC(t2);
    assert.equal(BLOCKED_EDGES.has(`${r1},${c1}|${r2},${c2}`), true);
    assert.equal(BLOCKED_EDGES.has(`${r2},${c2}|${r1},${c1}`), true);
  }
});

test('navBFS never crosses walls and never transits through START_POS or END_POS', () => {
  for (let r1 = 0; r1 < GRID_SIZE; r1++) {
    for (let c1 = 0; c1 < GRID_SIZE; c1++) {
      // Reachable from START_POS
      const fromStart = navBFS(START_POS[0], START_POS[1], r1, c1);
      assert.ok(fromStart.length > 0, `Cell (${r1},${c1}) unreachable from START_POS`);
      const startTrace = traceSteps(START_POS[0], START_POS[1], fromStart);
      assert.deepEqual(startTrace.at(-1), [r1, c1]);

      // Can reach END_POS
      const toEnd = navBFS(r1, c1, END_POS[0], END_POS[1]);
      assert.ok(toEnd.length > 0, `END_POS unreachable from (${r1},${c1})`);
      const endTrace = traceSteps(r1, c1, toEnd);
      assert.deepEqual(endTrace.at(-1), END_POS);

      // Pairwise reachability without transiting through START_POS / END_POS
      for (let r2 = 0; r2 < GRID_SIZE; r2++) {
        for (let c2 = 0; c2 < GRID_SIZE; c2++) {
          if (r1 === r2 && c1 === c2) continue;
          const steps = navBFS(r1, c1, r2, c2);
          assert.ok(steps.length > 0, `No path from (${r1},${c1}) to (${r2},${c2})`);
          const coords = traceSteps(r1, c1, steps);
          assert.deepEqual(coords.at(-1), [r2, c2]);
          for (const [rr, cc] of coords) {
            assert.ok(
              rr >= 0 && rr < GRID_SIZE && cc >= 0 && cc < GRID_SIZE,
              `Interior path transited outside grid via (${rr},${cc})`
            );
          }
        }
      }
    }
  }
});

test('compressSteps collapses orthogonal runs and preserves individual diagonals', () => {
  assert.deepEqual(compressSteps(['N', 'N', 'N']), ['3 N']);
  assert.deepEqual(compressSteps(['NE', 'NE']), ['1 NE', '1 NE']);
  assert.deepEqual(compressSteps(['E', 'E', 'SE', 'S', 'S']), ['2 E', '1 SE', '2 S']);
  assert.deepEqual(compressSteps([]), []);
});

test('segmentsIntersect detects crossings, T-intersections, and collinear overlaps', () => {
  assert.equal(segmentsIntersect([0, 0], [2, 2], [0, 2], [2, 0]), true);
  assert.equal(segmentsIntersect([0, 0], [0, 4], [0, 2], [2, 2]), true);
  assert.equal(segmentsIntersect([0, 0], [0, 2], [1, 0], [1, 2]), false);
});

test('findNonCrossingPath rejects 180-degree collinear reversals', () => {
  // Only one possible placement for A, B, C in a row: (2,2) -> (2,3) -> (2,0)
  // Segment (2,3)->(2,0) doubles back over (2,2)->(2,3)
  const letterCells = {
    A: [[2, 2]],
    B: [[2, 3]],
    C: [[2, 0]],
  };
  assert.equal(findNonCrossingPath('ABC', letterCells), null);
});

test('computeRequired takes the per-letter max across words', () => {
  assert.deepEqual(computeRequired(['HELPFUL', 'BRAVE']), {
    H: 1, E: 1, L: 2, P: 1, F: 1, U: 1, B: 1, R: 1, A: 1, V: 1,
  });
});

test('generate produces valid non-crossing grids and rejects >25 required letters', () => {
  const result = generate(['HELPFUL', 'THRIFTY', 'BRAVE']);
  assert.equal(result.error, undefined);
  assert.equal(result.grid.length, GRID_SIZE);
  assert.equal(result.grid.flat().length, GRID_CELLS);

  for (const word of result.orderedWords) {
    const pos = result.placements[word].positions;
    assert.equal(pos.length, word.length);
    const seen = new Set();
    pos.forEach(([r, c], idx) => {
      assert.equal(result.grid[r][c], word[idx]);
      const key = `${r},${c}`;
      assert.equal(seen.has(key), false, `Reused cell ${key} in word ${word}`);
      seen.add(key);
    });
    for (let i = 0; i < pos.length - 1; i++) {
      for (let j = i + 2; j < pos.length - 1; j++) {
        assert.equal(
          segmentsIntersect(pos[i], pos[i + 1], pos[j], pos[j + 1]),
          false,
          `Self-crossing segments in ${word}`
        );
      }
    }
    const dirs = computeWordDirections(pos);
    assert.equal(dirs.length, word.length + 1);
    assert.ok(dirs.every(d => d.length > 0));
  }

  // 26 distinct letters cannot fit in a 25-cell grid
  const tooMany = generate(['ABCDEFGH', 'IJKLMNOP', 'QRSTUVWX', 'YZ']);
  assert.match(tooMany.error, /at least 26 letter cells/);
});

test('generate handles repeated-letter stress input without hanging', () => {
  const start = Date.now();
  const result = generate(['AAAAAAAA']);
  const elapsed = Date.now() - start;
  assert.ok(elapsed < 2000, `generate('AAAAAAAA') took too long (${elapsed}ms)`);
  assert.ok(result.grid || result.error);
});

test('parseInput strips non-letters, uppercases, and deduplicates', () => {
  const parsed = parseInput('  helpful! \nTHRIFTY\nhelpful\n123\n  bra-ve  ');
  assert.deepEqual(parsed.words, ['HELPFUL', 'THRIFTY', 'BRAVE']);
  assert.equal(parsed.strippedChars, true);
  assert.equal(parsed.removedDuplicates, 1);
});

test('escapeHtml escapes HTML special characters', () => {
  assert.equal(escapeHtml(`<script>"a"&'b'</script>`), '&lt;script&gt;&quot;a&quot;&amp;&#39;b&#39;&lt;/script&gt;');
});

test('encodeMazeState and decodeMazeState round-trip exact grid, words, and positions', () => {
  const original = generate(['HELPFUL', 'THRIFTY', 'BRAVE']);
  assert.equal(original.error, undefined);

  const code = encodeMazeState(original);
  assert.ok(code.length <= 65, `Expected compact code, got length ${code.length}`);

  const decoded = decodeMazeState(`#m=${code}`);
  assert.deepEqual(decoded, original);
  assert.deepEqual(decodeMazeState(code), original);
});

test('decodeMazeState rejects malformed, out-of-range, and duplicate-cell codes', () => {
  assert.equal(decodeMazeState(''), null);
  assert.equal(decodeMazeState('#m=TOO_SHORT.012'), null);
  // Duplicate cell index '0' in one word
  assert.equal(decodeMazeState('ABCDEFGHIJKLMNOPQRSTUVWXY.001'), null);
  // Out-of-range base-36 char 'z' (>24)
  assert.equal(decodeMazeState('ABCDEFGHIJKLMNOPQRSTUVWXY.01z'), null);
  // More than 4 words
  assert.equal(decodeMazeState('ABCDEFGHIJKLMNOPQRSTUVWXY.0,1,2,3,4'), null);
  // Duplicate words reconstructed from different positions
  assert.equal(decodeMazeState('AAAAAAAAAAAAAAAAAAAAAAAAA.01,23'), null);
});

test('buildPrintHTML produces balanced sheets, viewBox SVGs, and valid inline script', () => {
  const result = generate(['HELPFUL', 'THRIFTY', 'BRAVE']);
  assert.equal(result.error, undefined);

  const html = buildPrintHTML(result);
  assert.match(html, /<meta name="viewport"/);
  assert.match(html, /viewBox="0 0 424 436"/);
  assert.match(html, /<main id="sheets">/);

  // Exact section counts: 1 Coordinator + 3 Easy + 3 Hard + 9 Sign & Letter Card pages = 16
  assert.equal((html.match(/class="page section-coord"/g) || []).length, 1);
  assert.equal((html.match(/class="page section-easy"/g) || []).length, 3);
  assert.equal((html.match(/class="page section-hard"/g) || []).length, 3);
  assert.equal((html.match(/class="lc-page section-cards"/g) || []).length, 9);

  // No red direct-path <path> lines in print output
  assert.equal(html.includes('<path '), false);

  // Inline toolbar script parses cleanly
  const scriptMatch = html.match(/<script>([\s\S]*?)<\/script>/);
  assert.ok(scriptMatch, 'Expected inline script in print HTML');
  assert.doesNotThrow(() => new Function(scriptMatch[1]));
});
