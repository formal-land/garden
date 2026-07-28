FROM rocq/rocq-prover:9.0.1-ocaml-4.14.2-flambda

LABEL org.opencontainers.image.source="https://github.com/formal-land/garden"
LABEL org.opencontainers.image.description="Rocq dependencies for Garden CI"

COPY --chown=rocq:rocq rocq-garden.opam /tmp/rocq-garden.opam

RUN ulimit -s unlimited \
    && opam install -y --jobs=4 --deps-only /tmp/rocq-garden.opam \
    && opam clean --all-switches --download-cache --logs -y
