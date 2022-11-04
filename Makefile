###############################
# Common defaults/definitions #
###############################

comma := ,

# Checks two given strings for equality.
eq = $(if $(or $(1),$(2)),$(and $(findstring $(1),$(2)),\
                                $(findstring $(2),$(1))),1)




###########
# Aliases #
###########


docs: cargo.doc


fmt: cargo.fmt


fuzz: cargo.fuzz


lint: cargo.lint


test: test.cargo




##################
# Cargo commands #
##################

# Generate crate documentation from Rust sources.
#
# Usage:
#	make cargo.doc [private=(yes|no)] [docsrs=(no|yes)]
#	               [open=(yes|no)] [clean=(no|yes)]

cargo.doc:
ifeq ($(clean),yes)
	@rm -rf target/doc/
endif
	$(if $(call eq,$(docsrs),yes),RUSTDOCFLAGS='--cfg docsrs',) \
	cargo $(if $(call eq,$(docsrs),yes),+nightly,) doc -p cucumber-expressions \
		--all-features \
		$(if $(call eq,$(private),no),,--document-private-items) \
		$(if $(call eq,$(open),no),,--open)


# Format Rust sources with rustfmt.
#
# Usage:
#	make cargo.fmt [check=(no|yes)]

cargo.fmt:
	cargo +nightly fmt --all $(if $(call eq,$(check),yes),-- --check,)


# Fuzz Rust sources with cargo-fuzz.
#
# Usage:
#	make cargo.fuzz target=<fuzz-target> [time=<timeout>]

cargo.fuzz:
	cargo +nightly fuzz run $(target) \
		$(if $(call eq,$(time),),,-- -max_total_time=$(time))


# Lint Rust sources with Clippy.
#
# Usage:
#	make cargo.lint

cargo.lint:
	cargo clippy -p cucumber-expressions --all-features -- -D warnings


cargo.test: test.cargo




####################
# Testing commands #
####################

# Run Rust tests of project crate.
#
# Usage:
#	make test.cargo [careful=(no|yes)]

test.cargo:
ifeq ($(careful),yes)
ifeq ($(shell cargo install --list | grep cargo-careful),)
	cargo install cargo-careful
endif
ifeq ($(shell rustup component list --toolchain=nightly \
              | grep 'rust-src (installed)'),)
	rustup component add --toolchain=nightly rust-src
endif
endif
	cargo $(if $(call eq,$(careful),yes),+nightly careful,) test \
		-p cucumber-expressions \
		--all-features




##################
# .PHONY section #
##################

.PHONY: docs fmt fuzz lint test \
        cargo.doc cargo.fmt cargo.fuzz cargo.lint cargo.test \
        test.cargo
