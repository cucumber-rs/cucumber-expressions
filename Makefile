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


lint: cargo.lint


fuzz: cargo.fuzz


test: test.cargo




##################
# Cargo commands #
##################

# Generate crate documentation from Rust sources.
#
# Usage:
#	make cargo.doc [private=(yes|no)]
#	               [open=(yes|no)] [clean=(no|yes)]

cargo.doc:
ifeq ($(clean),yes)
	@rm -rf target/doc/
endif
	cargo doc --all-features \
		$(if $(call eq,$(private),no),,--document-private-items) \
		$(if $(call eq,$(open),no),,--open)


# Format Rust sources with rustfmt.
#
# Usage:
#	make cargo.fmt [check=(no|yes)]

cargo.fmt:
	cargo +nightly fmt $(if $(call eq,$(check),yes),-- --check,)


# Lint Rust sources with Clippy.
#
# Usage:
#	make cargo.lint

cargo.lint:
	cargo clippy --all-features -- -D warnings


# Fuzz Rust sources with cargo-fuzz.
#
# Usage:
#	make cargo.fuzz target=<target-name> [time=<timeout>]

cargo.fuzz:
	cargo +nightly fuzz run $(target) \
		$(if $(call eq,$(time),),,-- -max_total_time=$(time))


cargo.test: test.cargo




####################
# Testing commands #
####################

# Run Rust tests of project crate.
#
# Usage:
#	make test.cargo

test.cargo:
	cargo test --all-features




##################
# .PHONY section #
##################

.PHONY: docs fmt lint test \
        cargo.doc cargo.fmt cargo.lint cargo.test \
        test.cargo
