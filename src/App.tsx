import { Navigate, Route, Routes } from "react-router-dom";
import { Nav } from "./components/Nav";
import { WalkPage } from "./pages/WalkPage";
import { LockIPage } from "./pages/LockIPage";
import { LockPiPage } from "./pages/LockPiPage";
import { SolvePage } from "./pages/SolvePage";
import { NotesPage } from "./pages/NotesPage";

export default function App() {
  return (
    <div className="app-shell">
      <Nav />
      <Routes>
        <Route path="/" element={<WalkPage />} />
        <Route path="/lock-i" element={<LockIPage />} />
        <Route path="/lock-pi" element={<LockPiPage />} />
        <Route path="/solve" element={<SolvePage />} />
        <Route path="/notes" element={<NotesPage />} />
        {/* Legacy routes from the pre-realignment UI */}
        <Route path="/lock" element={<Navigate to="/lock-i" replace />} />
        <Route path="/split" element={<Navigate to="/" replace />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </div>
  );
}
