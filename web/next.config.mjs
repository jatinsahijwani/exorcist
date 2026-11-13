// Static export for GitHub Pages. The site lives under /exorcist on github.io; set
// EXORCIST_BASE_PATH="" to serve it at the root locally.
const basePath = process.env.EXORCIST_BASE_PATH ?? "/exorcist";

export default {
  output: "export",
  basePath,
  trailingSlash: true,
  images: { unoptimized: true },
  poweredByHeader: false,
  env: { NEXT_PUBLIC_BASE_PATH: basePath },
};
