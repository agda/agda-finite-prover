all: test
.PHONY: all deps test clean clobber

deps: src/find_deps.rb
	$< > $@

include deps

test: $(patsubst src/%.hs,crumbs/%.agda,$(shell find src -name '*.hs'))
	cd crumbs; agda `find -name '*.agda'`
	-@echo '*** ALL TESTS OK ***'

clean:
	rm -rf crumbs

clobber: clean
	rm -rf deps
