# Anonymised artefact build for double-blind submission.
#
# Produces `blocksynchroniser-artifact.zip` containing a standalone, buildable
# Lean project with all author-identifying material stripped: copyright lines
# replaced with "Anonymous", AI-tool acknowledgements anonymised, and all
# process / docs / changelog / Aristotle-workflow files excluded.

ARTIFACT_NAME := blocksynchroniser-artifact
STAGING       := /tmp/$(ARTIFACT_NAME)
ZIP           := $(ARTIFACT_NAME).zip

.PHONY: artifact clean-artifact

artifact: clean-artifact
	@echo "[artifact] staging at $(STAGING)"
	@mkdir -p $(STAGING)
	# Copy the buildable Lean project (sources + manifest + toolchain).
	@cp -R BlockSynchroniser $(STAGING)/
	@cp BlockSynchroniser.lean Main.lean lakefile.lean lake-manifest.json \
	    lean-toolchain README.md formalization.md $(STAGING)/
	# Minimal .gitignore for the standalone project.
	@printf '/.lake\n.DS_Store\n*.zip\n' > $(STAGING)/.gitignore
	# Strip author names from every source-file copyright line.
	@find $(STAGING) -name '*.lean' -exec \
	    sed -i.bak 's/Copyright Ilya Sergey/Copyright Anonymous/g' {} +
	@find $(STAGING) -name '*.bak' -delete
	# Anonymise the README acknowledgement (drop tool / vendor names).
	@printf '%s\n' \
	    '## Acknowledgements' \
	    '' \
	    'The Lean proofs in this repository were produced with the help of' \
	    'automated proof-assistance tools.' \
	    > $(STAGING)/README.md.ack
	@awk '/^## Acknowledgements$$/{exit} {print}' $(STAGING)/README.md \
	    > $(STAGING)/README.md.head
	@cat $(STAGING)/README.md.head $(STAGING)/README.md.ack > $(STAGING)/README.md
	@rm $(STAGING)/README.md.head $(STAGING)/README.md.ack
	# Sanity check: nothing identifying remains.
	@if grep -rE 'Ilya Sergey|ilya\.sergey|ilyas239|aristotle\.harmonic|Aristotle|Harmonic|Anthropic|Claude' \
	      $(STAGING) > /dev/null 2>&1; then \
	    echo "[artifact] FAIL: identifying material still present:"; \
	    grep -rnE 'Ilya Sergey|ilya\.sergey|ilyas239|aristotle\.harmonic|Aristotle|Harmonic|Anthropic|Claude' \
	      $(STAGING); \
	    exit 1; \
	fi
	# Bundle.
	@cd /tmp && zip -qr $(ZIP) $(ARTIFACT_NAME)
	@mv /tmp/$(ZIP) ./
	@rm -rf $(STAGING)
	@echo "[artifact] $(ZIP) ($$(du -h $(ZIP) | cut -f1))"

clean-artifact:
	@rm -rf $(STAGING) $(ZIP)
