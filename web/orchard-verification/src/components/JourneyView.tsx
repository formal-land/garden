import {
  useCallback,
  useEffect,
  useRef,
  useState,
} from "react";
import type { JourneyStage, OrchardVerificationData } from "../data/model";
import {
  EvidencePanel,
  RepositoryBadges,
  StatusBadge,
  statusLabels,
} from "./EvidencePanel";
import { ProofMap } from "./ProofMap";
import { DevelopmentSummary, WorkUnitPanel } from "./WorkHistory";

const BASE_STAGE_DURATION = 9_000;

function stageDuration(stage: JourneyStage) {
  return Math.min(
    13_000,
    BASE_STAGE_DURATION + Math.max(0, stage.nodeIds.length - 3) * 650,
  );
}

function stageFromHash(stages: readonly JourneyStage[]) {
  const match = window.location.hash.match(/(?:^#|&)stage=([^&]+)/);
  if (!match) return -1;
  const requested = decodeURIComponent(match[1]);
  return stages.findIndex((stage) => stage.id === requested);
}

export function JourneyView({ data }: { data: OrchardVerificationData }) {
  const initialIndex = Math.max(0, stageFromHash(data.stages));
  const [stageIndex, setStageIndex] = useState(initialIndex);
  const [progress, setProgress] = useState(0);
  const [playing, setPlaying] = useState(false);
  const [progressive, setProgressive] = useState(false);
  const [ended, setEnded] = useState(false);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [reducedMotion, setReducedMotion] = useState(
    () => window.matchMedia("(prefers-reduced-motion: reduce)").matches,
  );
  const [evidenceOpen, setEvidenceOpen] = useState(
    () => !window.matchMedia("(max-width: 760px)").matches,
  );
  const shellRef = useRef<HTMLElement | null>(null);
  const frameRef = useRef<number | null>(null);
  const startedAtRef = useRef(0);
  const progressRef = useRef(0);
  const resumeOnVisible = useRef(false);
  const timelineButtons = useRef<Array<HTMLButtonElement | null>>([]);
  const stage = data.stages[stageIndex];
  const duration = stageDuration(stage);

  const updateProgress = useCallback((nextProgress: number) => {
    progressRef.current = nextProgress;
    setProgress(nextProgress);
  }, []);

  const stopAnimation = useCallback(() => {
    if (frameRef.current !== null) cancelAnimationFrame(frameRef.current);
    frameRef.current = null;
  }, []);

  const pause = useCallback(() => {
    stopAnimation();
    setPlaying(false);
  }, [stopAnimation]);

  const goTo = useCallback(
    (nextIndex: number, options?: { progressive?: boolean }) => {
      const bounded = Math.max(0, Math.min(data.stages.length - 1, nextIndex));
      pause();
      setStageIndex(bounded);
      updateProgress(0);
      setProgressive(Boolean(options?.progressive));
      setEnded(false);
    },
    [data.stages.length, pause, updateProgress],
  );

  useEffect(() => {
    const hash = `#stage=${encodeURIComponent(stage.id)}`;
    window.history.replaceState(null, "", hash);
  }, [stage.id]);

  useEffect(() => {
    const currentButton = timelineButtons.current[stageIndex];
    if (typeof currentButton?.scrollIntoView !== "function") return;
    currentButton.scrollIntoView({
      block: "nearest",
      inline: "center",
      behavior: reducedMotion ? "auto" : "smooth",
    });
  }, [reducedMotion, stageIndex]);

  useEffect(() => {
    const query = window.matchMedia("(prefers-reduced-motion: reduce)");
    const onChange = (event: MediaQueryListEvent) => {
      setReducedMotion(event.matches);
      if (event.matches) setProgressive(false);
    };
    query.addEventListener("change", onChange);
    return () => query.removeEventListener("change", onChange);
  }, []);

  useEffect(() => {
    const query = window.matchMedia("(max-width: 760px)");
    const onChange = (event: MediaQueryListEvent) => setEvidenceOpen(!event.matches);
    query.addEventListener("change", onChange);
    return () => query.removeEventListener("change", onChange);
  }, []);

  useEffect(() => {
    if (!playing) return undefined;

    if (reducedMotion) {
      const remainingDuration = Math.max(
        1_000,
        duration * (1 - progressRef.current),
      );
      const timer = window.setTimeout(() => {
        if (stageIndex === data.stages.length - 1) {
          updateProgress(1);
          setEnded(true);
          setPlaying(false);
          return;
        }
        setStageIndex((current) => current + 1);
        updateProgress(0);
        setProgressive(false);
      }, remainingDuration);
      return () => window.clearTimeout(timer);
    }

    startedAtRef.current = performance.now() - progressRef.current * duration;

    const tick = (timestamp: number) => {
      const nextProgress = (timestamp - startedAtRef.current) / duration;
      if (nextProgress >= 1) {
        if (stageIndex === data.stages.length - 1) {
          updateProgress(1);
          setEnded(true);
          setPlaying(false);
          frameRef.current = null;
          return;
        }
        setStageIndex((current) => current + 1);
        updateProgress(0);
        setProgressive(true);
        startedAtRef.current = timestamp;
      } else {
        updateProgress(nextProgress);
      }
      frameRef.current = requestAnimationFrame(tick);
    };

    frameRef.current = requestAnimationFrame(tick);
    return stopAnimation;
  }, [
    data.stages.length,
    duration,
    playing,
    reducedMotion,
    stageIndex,
    stopAnimation,
    updateProgress,
  ]);

  const toggleTour = useCallback(() => {
    if (playing) {
      pause();
      return;
    }

    if (ended) {
      goTo(0, { progressive: !reducedMotion });
    } else {
      setProgressive(!reducedMotion);
    }
    setPlaying(true);
  }, [ended, goTo, pause, playing, reducedMotion]);

  useEffect(() => {
    const onKeyDown = (event: KeyboardEvent) => {
      const target = event.target as HTMLElement;
      if (/INPUT|SELECT|TEXTAREA|BUTTON/.test(target.tagName)) return;
      if (event.key === "ArrowLeft") goTo(stageIndex - 1);
      if (event.key === "ArrowRight") goTo(stageIndex + 1);
      if (event.key === " ") {
        event.preventDefault();
        toggleTour();
      }
    };
    document.addEventListener("keydown", onKeyDown);
    return () => document.removeEventListener("keydown", onKeyDown);
  }, [goTo, stageIndex, toggleTour]);

  useEffect(() => {
    const onVisibilityChange = () => {
      if (document.hidden && playing) {
        resumeOnVisible.current = true;
        pause();
      } else if (!document.hidden && resumeOnVisible.current) {
        resumeOnVisible.current = false;
        setPlaying(true);
      }
    };
    document.addEventListener("visibilitychange", onVisibilityChange);
    return () => document.removeEventListener("visibilitychange", onVisibilityChange);
  }, [pause, playing]);

  useEffect(() => {
    const onFullscreenChange = () => {
      setIsFullscreen(document.fullscreenElement === shellRef.current);
    };
    document.addEventListener("fullscreenchange", onFullscreenChange);
    return () => document.removeEventListener("fullscreenchange", onFullscreenChange);
  }, []);

  const priorNodes = data.stages
    .slice(0, stageIndex)
    .flatMap((item) => item.nodeIds);
  const activeNodeIndex = Math.min(
    stage.nodeIds.length - 1,
    Math.floor(Math.min(progress, 0.999_999) * Math.max(1, stage.nodeIds.length)),
  );
  const usesProgressiveReveal = progressive && !reducedMotion;
  const currentReveal = usesProgressiveReveal
    ? stage.nodeIds.slice(0, activeNodeIndex + 1)
    : stage.nodeIds;
  const focusNodes = usesProgressiveReveal
    ? stage.nodeIds.slice(Math.max(0, activeNodeIndex - 1), activeNodeIndex + 1)
    : stage.nodeIds;
  const revealedNodes = [...new Set([...priorNodes, ...currentReveal])];
  const focusedEvidenceNodes = focusNodes.flatMap((nodeId) => {
    const node = data.nodes.find(({ id }) => id === nodeId);
    return node ? [node] : [];
  });

  const onTimelineKeyDown = (
    event: React.KeyboardEvent<HTMLButtonElement>,
    index: number,
  ) => {
    let nextIndex: number | null = null;
    if (event.key === "ArrowLeft") nextIndex = Math.max(0, index - 1);
    if (event.key === "ArrowRight") {
      nextIndex = Math.min(data.stages.length - 1, index + 1);
    }
    if (event.key === "Home") nextIndex = 0;
    if (event.key === "End") nextIndex = data.stages.length - 1;
    if (nextIndex === null) return;

    event.preventDefault();
    goTo(nextIndex);
    window.requestAnimationFrame(() => timelineButtons.current[nextIndex]?.focus());
  };

  const toggleFullscreen = async () => {
    const shell = shellRef.current;
    if (!shell || !document.fullscreenEnabled) return;
    if (document.fullscreenElement) await document.exitFullscreen();
    else await shell.requestFullscreen();
  };

  return (
    <main
      id="main-content"
      className="journey-shell"
      ref={shellRef}
      tabIndex={-1}
    >
      <section className="journey-intro" aria-labelledby="journey-title">
        <p className="eyebrow">Garden · Rocq · Evidence snapshot {data.snapshot.asOf}</p>
        <h1 id="journey-title">Orchard Verification Journey</h1>
        <p>
          A {data.stages.length}-stage account of how the post-NU6.2 Orchard Action
          implementation was captured in Rocq and connected to public-output and
          balance arguments.
        </p>
      </section>

      <DevelopmentSummary data={data} />

      <section className="transport" aria-label="Journey controls">
        <div className="transport__buttons">
          <button
            className="icon-button"
            type="button"
            onClick={() => goTo(stageIndex - 1)}
            disabled={stageIndex === 0}
            aria-label="Previous stage"
            title="Previous stage"
          >
            <span aria-hidden="true">←</span>
            <span className="icon-button__label">Previous</span>
          </button>
          <p className="transport__stage" aria-live="polite" aria-atomic="true">
            Stage {stageIndex + 1} of {data.stages.length}
          </p>
          <button
            className="icon-button"
            type="button"
            onClick={() => goTo(stageIndex + 1)}
            disabled={stageIndex === data.stages.length - 1}
            aria-label="Next stage"
            title="Next stage"
          >
            <span className="icon-button__label">Next</span>
            <span aria-hidden="true">→</span>
          </button>
          <button
            className="play-button"
            type="button"
            onClick={toggleTour}
            aria-label={ended ? "Replay tour" : playing ? "Pause tour" : "Play tour"}
            aria-pressed={playing}
          >
            <span aria-hidden="true">{ended ? "↻" : playing ? "Ⅱ" : "▶"}</span>
            {ended ? "Replay tour" : playing ? "Pause tour" : "Play tour"}
          </button>
          <button
            className="icon-button fullscreen-button"
            type="button"
            onClick={toggleFullscreen}
            aria-label={isFullscreen ? "Exit full screen" : "Full screen"}
            aria-pressed={isFullscreen}
            title={isFullscreen ? "Exit full screen" : "Full screen"}
          >
            <span aria-hidden="true">⛶</span>
            <span className="icon-button__label">
              {isFullscreen ? "Exit full screen" : "Full screen"}
            </span>
          </button>
        </div>
      </section>

      <nav className="stage-timeline" aria-label="Verification journey stages">
        {data.stages.map((item, index) => (
          <button
            type="button"
            key={item.id}
            ref={(button) => {
              timelineButtons.current[index] = button;
            }}
            className={`stage-step ${index < stageIndex ? "stage-step--past" : ""} ${
              index === stageIndex ? "stage-step--current" : ""
            }`}
            onClick={() => goTo(index)}
            onKeyDown={(event) => onTimelineKeyDown(event, index)}
            aria-current={index === stageIndex ? "step" : undefined}
            aria-label={`Stage ${index + 1}: ${item.title}. ${item.date}`}
            tabIndex={index === stageIndex ? 0 : -1}
            title={`${item.title} · ${item.date}`}
          >
            <span className="stage-step__number">Stage {index + 1}</span>
            <span className="stage-step__label">{item.title}</span>
            <span className="stage-step__date">{item.date}</span>
            <span className="stage-step__work">
              {item.workUnitIds.length} {item.workUnitIds.length === 1 ? "work unit" : "work units"}
            </span>
          </button>
        ))}
      </nav>

      <article
        className="stage-story"
        aria-labelledby={`journey-stage-title-${stage.id}`}
        key={stage.id}
      >
        <div className="stage-story__copy">
          <header className="stage-story__header">
            <p className="chapter-label">
              Stage {stage.ordinal} · {stage.date}
            </p>
            <h2 id={`journey-stage-title-${stage.id}`}>{stage.title}</h2>
            <p className="stage-story__theme">{stage.eyebrow}</p>
            <p className="stage-purpose">{stage.purpose}</p>
            <div className="stage-story__meta">
              <StatusBadge status={stage.status} />
              <RepositoryBadges data={data} repoIds={stage.repoIds} />
            </div>
          </header>
          <section
            className="stage-story__narrative"
            aria-labelledby={`journey-stage-claim-${stage.id}`}
          >
            <h3 id={`journey-stage-claim-${stage.id}`}>Claim and context</h3>
            <blockquote>{stage.claim}</blockquote>
            <p>{stage.narrative}</p>
          </section>
        </div>
        <div className="stage-story__work">
          <WorkUnitPanel data={data} workUnitIds={stage.workUnitIds} />
        </div>
        <details
          className="stage-story__evidence"
          open={evidenceOpen}
          onToggle={(event) => setEvidenceOpen(event.currentTarget.open)}
        >
          <summary>Evidence ({stage.evidenceIds.length})</summary>
          <EvidencePanel data={data} evidenceIds={stage.evidenceIds} />
        </details>
        <div className="stage-story__outcomes">
          <section>
            <h3>Established in this stage</h3>
            <ul className="fact-list fact-list--established">
              {stage.established.map((fact) => (
                <li key={fact}>{fact}</li>
              ))}
            </ul>
          </section>
          <section>
            <h3>Not yet established</h3>
            <ul className="fact-list fact-list--carried">
              {stage.carried.map((fact) => (
                <li key={fact}>{fact}</li>
              ))}
            </ul>
          </section>
        </div>
      </article>

      <section
        className={`journey-map journey-visual ${
          stage.nodeIds.length === 0 ? "journey-visual--empty" : ""
        }`}
        aria-label={`Evidence path for stage ${stageIndex + 1}: ${stage.title}`}
      >
        {stage.nodeIds.length > 0 ? (
          <>
            <div className="journey-visual__graph">
              <ProofMap
                data={data}
                compact
                focusNodeIds={focusNodes}
                revealedNodeIds={revealedNodes}
              />
            </div>
            <ul className="journey-visual__list" aria-label="Proof nodes in this stage">
              {focusedEvidenceNodes.map((node) => (
                <li className={`journey-visual__node journey-visual__node--${node.status}`} key={node.id}>
                  <span className="journey-visual__node-dot" aria-hidden="true" />
                  <span>
                    <strong>{node.title}</strong>
                    <small>
                      {statusLabels[node.status]} · {node.repoIds
                        .map((repoId) => data.repositories.find(({ id }) => id === repoId)?.shortName ?? repoId)
                        .join(", ")}
                    </small>
                  </span>
                </li>
              ))}
            </ul>
          </>
        ) : (
          <div className="journey-visual__empty" role="status">
            <h2>No visualization for this stage</h2>
            <p>The evidence and claims remain available in this stage.</p>
          </div>
        )}
      </section>
    </main>
  );
}
