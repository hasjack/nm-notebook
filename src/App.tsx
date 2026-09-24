import { Navigate, Route, Routes } from "react-router-dom";
import { AppLayout } from "./components/Nav";
import { HomePage } from "./pages/HomePage";
import { AlphabetPage } from "./pages/AlphabetPage";
import { MagnitudePage } from "./pages/MagnitudePage";
import { BeaconSpinePage } from "./pages/BeaconSpinePage";
import { RotationPage } from "./pages/RotationPage";
import { PhysicsPage } from "./pages/PhysicsPage";
import { Analysis1Page } from "./pages/Analysis1Page";
import { Analysis2Page } from "./pages/Analysis2Page";
import { Analysis3Page } from "./pages/Analysis3Page";
import { Analysis4Page } from "./pages/Analysis4Page";
import { Analysis5Page } from "./pages/Analysis5Page";
import { SolvePage } from "./pages/SolvePage";
import { CataloguePage } from "./pages/CataloguePage";
import { NotesPage } from "./pages/NotesPage";
import { NotesIndexPage } from "./pages/NotesIndexPage";
import { PrimesPage } from "./pages/PrimesPage";
import { SuperPrimesPage } from "./pages/SuperPrimesPage";
import { UnclaimedPage } from "./pages/UnclaimedPage";
import { BeaconSuperPage } from "./pages/BeaconSuperPage";
import { SuspectBenchPage } from "./pages/SuspectBenchPage";
import { MissedPage } from "./pages/MissedPage";
import { SpectrumPage } from "./pages/SpectrumPage";
import { Pm1TablePage } from "./pages/Pm1TablePage";
import { HirePage } from "./pages/HirePage";
import { BasinsPage } from "./pages/BasinsPage";
import { IslandsPage } from "./pages/IslandsPage";
import { CorridorPage } from "./pages/CorridorPage";
import { MicroscopePage } from "./pages/MicroscopePage";
import { CertificatesPage } from "./pages/CertificatesPage";
import { ZetaDoorsPage } from "./pages/ZetaDoorsPage";
import { Rank100Page } from "./pages/Rank100Page";
import { TwoClassCoveragePage } from "./pages/TwoClassCoveragePage";
import { CubeDoorPage } from "./pages/CubeDoorPage";
import { CoverageLatticePage } from "./pages/CoverageLatticePage";
import { DoorWaitsPage } from "./pages/DoorWaitsPage";
import { SubstackHireDoorsPage } from "./pages/SubstackHireDoorsPage";
import { GaussianDoorsPage } from "./pages/GaussianDoorsPage";
import { HireSpectrumPage } from "./pages/HireSpectrumPage";
import { HireLabPage } from "./pages/HireLabPage";
import { PaperPage } from "./pages/PaperPage";
import { WhenGoldDisconnectsPage } from "./pages/WhenGoldDisconnectsPage";
import { ZetaDoorsNotePage } from "./pages/ZetaDoorsNotePage";
import { SignedDoorsPage } from "./pages/SignedDoorsPage";
import { AlphabetSpiralPage } from "./pages/AlphabetSpiralPage";
import { CountPage } from "./pages/CountPage";
import { BellToyPage } from "./pages/BellToyPage";
import { AtlasPage } from "./pages/AtlasPage";
import { FlockersPage } from "./pages/FlockersPage";

export default function App() {
  return (
    <AppLayout>
      <Routes>
        <Route path="/" element={<HomePage />} />
        <Route path="/alphabet" element={<AlphabetPage />} />
        <Route path="/walk" element={<Navigate to="/alphabet?tab=walk" replace />} />
        <Route path="/lock-i" element={<Navigate to="/alphabet?tab=lock-i" replace />} />
        <Route path="/lock-pi" element={<Navigate to="/alphabet?tab=lock-pi" replace />} />
        <Route path="/free" element={<Navigate to="/alphabet?tab=free" replace />} />
        <Route path="/magnitude" element={<MagnitudePage />} />
        <Route path="/beacons" element={<BeaconSpinePage />} />
        <Route path="/rotation" element={<RotationPage />} />
        <Route path="/physics" element={<PhysicsPage />} />
        <Route path="/basel" element={<Navigate to="/alphabet?tab=basel" replace />} />
        <Route path="/analysis-1" element={<Analysis1Page />} />
        <Route path="/analysis-2" element={<Analysis2Page />} />
        <Route path="/analysis-3" element={<Analysis3Page />} />
        <Route path="/analysis-4" element={<Analysis4Page />} />
        <Route path="/analysis-5" element={<Analysis5Page />} />
        <Route path="/solve" element={<SolvePage />} />
        <Route path="/catalogue" element={<CataloguePage />} />
        <Route path="/primes" element={<PrimesPage />} />
        <Route path="/super-primes" element={<SuperPrimesPage />} />
        <Route path="/unclaimed" element={<UnclaimedPage />} />
        <Route path="/beacon-super" element={<BeaconSuperPage />} />
        <Route path="/suspect-bench" element={<SuspectBenchPage />} />
        <Route path="/missed" element={<MissedPage />} />
        <Route path="/spectrum" element={<SpectrumPage />} />
        <Route path="/pm1" element={<Pm1TablePage />} />
        <Route path="/hire" element={<HirePage />} />
        <Route path="/basins" element={<BasinsPage />} />
        <Route path="/islands" element={<IslandsPage />} />
        <Route path="/corridor" element={<CorridorPage />} />
        <Route path="/microscope" element={<MicroscopePage />} />
        <Route path="/certificates" element={<CertificatesPage />} />
        <Route path="/zeta-doors" element={<ZetaDoorsPage />} />
        <Route path="/rank100" element={<Rank100Page />} />
        <Route path="/two-class" element={<TwoClassCoveragePage />} />
        <Route path="/door-coverage" element={<TwoClassCoveragePage />} />
        <Route path="/cube-doors" element={<CubeDoorPage />} />
        <Route path="/coverage-lattice" element={<CoverageLatticePage />} />
        <Route path="/door-waits" element={<DoorWaitsPage />} />
        <Route path="/compose/hire-doors" element={<SubstackHireDoorsPage />} />
        <Route path="/gaussian-doors" element={<GaussianDoorsPage />} />
        <Route path="/certs" element={<Navigate to="/certificates" replace />} />
        <Route path="/hire-spectrum" element={<HireSpectrumPage />} />
        <Route path="/hire-lab" element={<HireLabPage />} />
        <Route path="/notes/hire-graph" element={<PaperPage />} />
        <Route path="/notes/when-gold-disconnects" element={<WhenGoldDisconnectsPage />} />
        <Route path="/notes/zeta-doors" element={<ZetaDoorsNotePage />} />
        <Route path="/paper" element={<Navigate to="/notes/hire-graph" replace />} />
        <Route
          path="/when-gold-disconnects"
          element={<Navigate to="/notes/when-gold-disconnects" replace />}
        />
        <Route path="/signed-doors" element={<SignedDoorsPage />} />
        <Route path="/alphabet-spiral" element={<AlphabetSpiralPage />} />
        <Route path="/count" element={<CountPage />} />
        <Route path="/notes" element={<NotesIndexPage />} />
        <Route path="/alphabet/notes" element={<NotesPage />} />
        <Route path="/toys/bell" element={<BellToyPage />} />
        <Route path="/toys/atlas" element={<AtlasPage />} />
        <Route path="/toys/flockers" element={<FlockersPage />} />
        <Route
          path="/notes/natural-mathematics-bell-toy"
          element={<Navigate to="/toys/bell" replace />}
        />
        <Route
          path="/notes/switching-quadratic-atlas-diagnostics"
          element={<Navigate to="/toys/atlas" replace />}
        />
        <Route path="/lock" element={<Navigate to="/alphabet?tab=lock-i" replace />} />
        <Route path="/split" element={<Navigate to="/alphabet?tab=free" replace />} />
        <Route path="*" element={<Navigate to="/" replace />} />
      </Routes>
    </AppLayout>
  );
}
