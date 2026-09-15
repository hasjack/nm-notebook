import { Navigate, Route, Routes } from "react-router-dom";
import { Nav } from "./components/Nav";
import { WalkPage } from "./pages/WalkPage";
import { LockPage } from "./pages/LockPage";
import { SplitPage } from "./pages/SplitPage";
import { NotesPage } from "./pages/NotesPage";

export default function App() {
  return (
    <div className="app-shell">
      <Nav />
      <Routes>
        <Route path="/" element={<WalkPage />} />
        <Route path="/lock" element={<LockPage />} />
        <Route path="/split" element={<SplitPage />} />
        <Route path="/notes" element={<NotesPage />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </div>
  );
}
