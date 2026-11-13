import { GHOST } from "./pixels";

/** The ghost mark as crisp SVG squares. */
export function GhostMark({ size = 18, className = "mark" }) {
  return (
    <svg className={className} width={size} height={size} viewBox={`0 0 ${GHOST.cols} ${GHOST.rows}`} aria-hidden shapeRendering="crispEdges">
      {GHOST.cells.map(([x, y]) => (
        <rect key={`${x}-${y}`} x={x} y={y} width={1} height={1} fill="currentColor" />
      ))}
    </svg>
  );
}
