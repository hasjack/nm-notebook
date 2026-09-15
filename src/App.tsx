import { Navigate, Route, Routes } from "react-router-dom";
import { Nav } from "./components/Nav";
import { WalkPage } from "./pages/WalkPage";
import { LockIPage } from "./pages/LockIPage";
import { LockPiPage } from "./pages/LockPiPage";
import { FreePage } from "./pages/FreePage";
import { MagnitudePage } from "./pages/MagnitudePage";
import { BaselPage } from "./pages/BaselPage";
import { Analysis1Page } from "./pages/Analysis1Page";
import { Analysis2Page } from "./pages/Analysis2Page";
import { Analysis3Page } from "./pages/Analysis3Page";
import { SolvePage } from "./pages/SolvePage";
import { CataloguePage } from "./pages/CataloguePage";
import { NotesPage } from "./pages/NotesPage";

export default function App() {
  return (
    <div className="app-shell">
      <Nav />
      <Routes>
        <Route path="/" element={<WalkPage />} />
        <Route path="/lock-i" element={<LockIPage />} />
        <Route path="/lock-pi" element={<LockPiPage />} />
        <Route path="/free" element={<FreePage />} />
        <Route path="/magnitude" element={<MagnitudePage />} />
        <Route path="/basel" element={<BaselPage />} />
        <Route path="/analysis-1" element={<Analysis1Page />} />
        <Route path="/analysis-2" element={<Analysis2Page />} />
        <Route path="/analysis-3" element={<Analysis3Page />} />
        <Route path="/solve" element={<SolvePage />} />
        <Route path="/catalogue" element={<CataloguePage />} />
        <Route path="/notes" element={<NotesPage />} />
        <Route path="/lock" element={<Navigate to="/lock-i" replace />} />
        <Route path="/split" element={<Navigate to="/free" replace />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </div>
  );
}
