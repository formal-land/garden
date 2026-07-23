import { useEffect, useMemo, useRef } from "react";
import gardenLogo from "../../../garden.svg?url";
import { orchardVerificationData } from "./data/content";
import { JourneyView } from "./components/JourneyView";
import { ProofMap } from "./components/ProofMap";
import { CircuitExplorer } from "./components/CircuitExplorer";
import { CircuitGrid } from "./components/CircuitGrid";

type View = "journey" | "atlas" | "circuit" | "grid";

function formatSnapshotDate(value: string): string {
  return new Intl.DateTimeFormat("en-GB", {
    day: "numeric",
    month: "short",
    year: "numeric",
    timeZone: "UTC",
  }).format(new Date(`${value}T00:00:00Z`));
}

function EvidenceContext() {
  const snapshot = orchardVerificationData.snapshot;
  const refs = snapshot.repositoryRefs;
  const detailsRef = useRef<HTMLDetailsElement>(null);

  useEffect(() => {
    const closeWhenPointerMovesOutside = (event: PointerEvent) => {
      const details = detailsRef.current;
      if (
        details?.open &&
        event.target instanceof Node &&
        !details.contains(event.target)
      ) {
        details.open = false;
      }
    };

    const closeOnEscape = (event: KeyboardEvent) => {
      const details = detailsRef.current;
      if (event.key !== "Escape" || !details?.open) return;

      details.open = false;
      details.querySelector("summary")?.focus();
    };

    document.addEventListener("pointerdown", closeWhenPointerMovesOutside);
    document.addEventListener("keydown", closeOnEscape);

    return () => {
      document.removeEventListener("pointerdown", closeWhenPointerMovesOutside);
      document.removeEventListener("keydown", closeOnEscape);
    };
  }, []);

  return (
    <details ref={detailsRef} className="evidence-context" id="evidence-context">
      <summary>
        <span>Snapshot</span>
        <time dateTime={snapshot.asOf}>{formatSnapshotDate(snapshot.asOf)}</time>
        <span className="evidence-context__short-refs" aria-hidden="true">
          Garden {refs.garden.slice(0, 6)}… · Halo2 {refs.halo2.slice(0, 6)}… · Orchard {refs.orchard.slice(0, 6)}…
        </span>
      </summary>
      <div className="evidence-context__panel">
        <div>
          <p className="context-label">Evidence status</p>
          <strong>{snapshot.title}</strong>
          <p>{snapshot.description}</p>
          <p className="evidence-context__caveat">{snapshot.caveat}</p>
        </div>
        <div>
          <p className="context-label">Repository versions</p>
          <dl className="revision-list">
            <div><dt>Garden</dt><dd><code title={refs.garden}>{refs.garden.slice(0, 8)}</code></dd></div>
            <div><dt>Halo2</dt><dd><code title={refs.halo2}>{refs.halo2.slice(0, 8)}</code></dd></div>
            <div><dt>Orchard</dt><dd><code title={refs.orchard}>{refs.orchard.slice(0, 8)}</code></dd></div>
          </dl>
        </div>
      </div>
    </details>
  );
}

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
        <a href="./circuit-grid.html" aria-current={view === "grid" ? "page" : undefined}>
          Grid
        </a>
      </nav>
      <EvidenceContext />
    </header>
  );
}

function AtlasView() {
  return (
    <main id="main-content" className="atlas-page" tabIndex={-1}>
      <section className="atlas-intro" aria-labelledby="atlas-title">
        <div>
          <p className="eyebrow">Verification atlas</p>
          <h1 id="atlas-title">Orchard Verification Atlas</h1>
          <p>
            Trace the evidence chain from implementation capture to protocol
            claims. Inspect any node to see its proof state, sources,
            dependencies, and open assumptions. Boundary nodes make the
            remaining trust assumptions explicit.
          </p>
        </div>
      </section>
      <ProofMap data={orchardVerificationData} />
    </main>
  );
}

function SiteFooter() {
  const snapshot = orchardVerificationData.snapshot;
  return (
    <footer className="site-footer">
      <p>
        Verification work by <strong>Formal Land</strong> · Garden framework · Snapshot{" "}
        <time dateTime={snapshot.asOf}>
          {formatSnapshotDate(snapshot.asOf)}
        </time>
      </p>
    </footer>
  );
}

export function App() {
  const view = useMemo<View>(
    () => {
      if (document.documentElement.dataset.view === "atlas") return "atlas";
      if (document.documentElement.dataset.view === "circuit") return "circuit";
      if (document.documentElement.dataset.view === "grid") return "grid";
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
      ) : view === "circuit" ? (
        <CircuitExplorer />
      ) : (
        <CircuitGrid />
      )}
      <SiteFooter />
    </div>
  );
}
