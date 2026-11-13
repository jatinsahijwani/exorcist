import "@fontsource-variable/jetbrains-mono";
import "@fontsource-variable/geist";
import "./globals.css";

export const metadata = {
  title: "Exorcist: ghost funds in NEAR contracts",
  description:
    "Exorcist finds ghost funds in NEAR contracts, or proves there are none: attack traces checked by the Lean kernel, proofs for all traces of a NEAR execution model, and replays on real Rust contracts.",
  icons: { icon: `${process.env.NEXT_PUBLIC_BASE_PATH}/favicon.svg` },
};

export const viewport = { themeColor: "#0f0f11", colorScheme: "dark" };

export default function RootLayout({ children }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
