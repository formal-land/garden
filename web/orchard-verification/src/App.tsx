import { useMemo } from "react";
import gardenLogo from "../../../garden.svg?url";
import footerGarden from "./assets/garden-footer.webp";
import { orchardVerificationData } from "./data/content";
import { JourneyView } from "./components/JourneyView";
import { ProofMap } from "./components/ProofMap";
import { CircuitExplorer } from "./components/CircuitExplorer";

type View = "journey" | "atlas" | "circuit";

function SiteHeader({ view }: { view: View }) {
  return (
    <header className="site-header">
      <a className="garden-brand" href="./" aria-label="Garden Orchard verification journey">
        <img src={gardenLogo} alt="" width="46" height="46" />
        <span>
          <strong>Garden</strong>
          <small>Orchard verification</small>
        </span>
      </a>
      <nav className="view-switcher" aria-label="Visualization views">
        <a href="./" aria-current={view === "journey" ? "page" : undefined}>
          Journey
        </a>
        <a href="./proof-map.html" aria-current={view === "atlas" ? "page" : undefined}>
          Atlas
        </a>
        <a href="./circuit.html" aria-current={view === "circuit" ? "page" : undefined}>
          Circuit
        </a>
      </nav>
    </header>
  );
}

function AtlasView() {
  return (
    <main id="main-content" className="atlas-page" tabIndex={-1}>
      <section className="atlas-intro" aria-labelledby="atlas-title">
        <div>
          <p className="eyebrow">The complete evidence landscape</p>
          <h1 id="atlas-title">Orchard Verification Atlas</h1>
          <p>
            Explore how implementation capture, checked parity, semantics,
            reusable gadget proofs, and protocol claims connect. The boundary
            nodes are part of the map on purpose.
          </p>
        </div>
        <a className="text-link" href="./">
          Watch the guided journey <span aria-hidden="true">→</span>
        </a>
      </section>
      <ProofMap data={orchardVerificationData} />
    </main>
  );
}

function SiteFooter() {
  const refs = orchardVerificationData.snapshot.repositoryRefs;
  return (
    <footer className="site-footer">
      <div className="site-footer__mark" aria-hidden="true">✦</div>
      <div>
        <strong>{orchardVerificationData.snapshot.title}</strong>
        <p>{orchardVerificationData.snapshot.description}</p>
      </div>
      <dl className="revision-list">
        <div><dt>Garden</dt><dd><code>{refs.garden.slice(0, 8)}</code></dd></div>
        <div><dt>Halo2</dt><dd><code>{refs.halo2.slice(0, 8)}</code></dd></div>
        <div><dt>Orchard</dt><dd><code>{refs.orchard.slice(0, 8)}</code></dd></div>
      </dl>
      <p className="site-footer__caveat">{orchardVerificationData.snapshot.caveat}</p>
      <div className="site-footer__art" aria-hidden="true">
        <img src={footerGarden} alt="" width="1600" height="533" loading="lazy" />
      </div>
    </footer>
  );
}

export function App() {
  const view = useMemo<View>(
    () => {
      if (document.documentElement.dataset.view === "atlas") return "atlas";
      if (document.documentElement.dataset.view === "circuit") return "circuit";
      return "journey";
    },
    [],
  );
  return (
    <div className="site-shell">
      <SiteHeader view={view} />
      {view === "journey" ? (
        <JourneyView data={orchardVerificationData} />
      ) : view === "atlas" ? (
        <AtlasView />
      ) : (
        <CircuitExplorer />
      )}
      <SiteFooter />
    </div>
  );
}
