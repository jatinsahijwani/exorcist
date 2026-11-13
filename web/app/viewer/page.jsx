import { Topbar } from "@/components/Topbar";
import { Viewer } from "@/components/Viewer";
import "./viewer.css";

export const metadata = {
  title: "Exorcist trace viewer",
  description: "Step through the ghost-funds attack Exorcist found on a minimal model of the Oct 2026 NEAR Intents mechanism, and the same attack failing on the fixed contract. Real exorcist output.",
};

export default function ViewerPage() {
  return (
    <>
      <Topbar current="viewer" />
      <main className="vw-main">
        <Viewer />
      </main>
    </>
  );
}
