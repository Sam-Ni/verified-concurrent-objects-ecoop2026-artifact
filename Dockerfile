FROM coqorg/coq:8.20.1

WORKDIR /home/coq/workspace

USER root

RUN apt-get update && apt-get install -y \
    emacs git \
    && rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/ProofGeneral/PG.git /opt/PG
RUN chown -R coq:coq /opt/PG

USER coq

COPY --chown=coq:coq . /home/coq/workspace

RUN mkdir -p ~/.emacs.d && echo '(load-file "/opt/PG/generic/proof-site.el")' >> ~/.emacs.d/init.el