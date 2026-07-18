import { useEffect, useMemo, useState } from "react";
import gardenLogo from "../../../garden.svg?url";
import { orchardVerificationData } from "./data/content";
import { JourneyView } from "./components/JourneyView";
import { ProofMap } from "./components/ProofMap";

type Theme = "light" | "dark";
type View = "journey" | "atlas";

function initialTheme(): Theme {
  const saved = window.localStorage.getItem("garden-orchard-theme");
  if (saved === "light" || saved === "dark") return saved;
  return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
}

function SiteHeader({ view, theme, onThemeChange }: {
  view: View;
  theme: Theme;
  onThemeChange: () => void;
}) {
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
      </nav>
      <button
        type="button"
        className="theme-toggle"
        onClick={onThemeChange}
        aria-label={`Use ${theme === "light" ? "dark" : "light"} theme`}
        title={`Use ${theme === "light" ? "dark" : "light"} theme`}
      >
        <span aria-hidden="true">{theme === "light" ? "☾" : "☀"}</span>
      </button>
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
    </footer>
  );
}

export function App() {
  const view = useMemo<View>(
    () => document.documentElement.dataset.view === "atlas" ? "atlas" : "journey",
    [],
  );
  const [theme, setTheme] = useState<Theme>(initialTheme);

  useEffect(() => {
    document.documentElement.dataset.theme = theme;
    window.localStorage.setItem("garden-orchard-theme", theme);
    document.querySelector('meta[name="theme-color"]')?.setAttribute(
      "content",
      theme === "light" ? "#f7f4e8" : "#0d1d15",
    );
  }, [theme]);

  return (
    <div className="site-shell">
      <SiteHeader
        view={view}
        theme={theme}
        onThemeChange={() => setTheme((current) => current === "light" ? "dark" : "light")}
      />
      {view === "journey" ? <JourneyView data={orchardVerificationData} /> : <AtlasView />}
      <SiteFooter />
    </div>
  );
}
