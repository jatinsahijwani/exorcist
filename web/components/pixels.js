// Pixel lettering for the EXORCIST wordmark and the ghost mark. Each glyph is a grid of
// "#" (lit) and "." (dark), 7 columns by 9 rows, with two-cell strokes so it reads at any size.

const GLYPHS = {
  E: ["#######", "#######", "##.....", "##.....", "######.", "##.....", "##.....", "#######", "#######"],
  X: ["##...##", "##...##", ".##.##.", "..###..", "..###..", "..###..", ".##.##.", "##...##", "##...##"],
  O: [".#####.", "#######", "##...##", "##...##", "##...##", "##...##", "##...##", "#######", ".#####."],
  R: ["######.", "#######", "##...##", "##...##", "######.", "#####..", "##.##..", "##..##.", "##...##"],
  C: [".######", "#######", "##.....", "##.....", "##.....", "##.....", "##.....", "#######", ".######"],
  I: ["######", "######", "..##..", "..##..", "..##..", "..##..", "..##..", "######", "######"],
  S: [".######", "#######", "##.....", "######.", ".######", ".....##", ".....##", "#######", "######."],
  T: ["#######", "#######", "..###..", "..###..", "..###..", "..###..", "..###..", "..###..", "..###.."],
};

/** Lit cells of a word, as [col, row], plus the grid size. */
export function wordCells(word = "EXORCIST") {
  const cells = [];
  let x = 0;
  for (const ch of word) {
    const g = GLYPHS[ch];
    g.forEach((line, y) => {
      for (let c = 0; c < line.length; c++) if (line[c] === "#") cells.push([x + c, y]);
    });
    x += g[0].length + 2;
  }
  return { cols: x - 2, rows: 9, cells };
}

/** The mark: a small ghost, 9 × 9. Eyes are holes. */
export const GHOST = (() => {
  const rows = ["..#####..", ".#######.", "#########", "##.###.##", "##.###.##", "#########", "#########", "#########", "#.##.##.#"];
  const cells = [];
  rows.forEach((l, y) => [...l].forEach((ch, x) => ch === "#" && cells.push([x, y])));
  return { cols: 9, rows: 9, cells };
})();

/** Deterministic pseudo-random numbers (mulberry32), so the layout is the same on every visit. */
export function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
