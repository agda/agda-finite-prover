all: recompute_deps test
.PHONY: all recompute_deps test clean clobber

recompute_deps:
	rm -rf deps

deps: src/find_deps.rb
	$< > $@

include deps

test: crumbs/Main.agda
	cd crumbs; agda --include-path=. --include-path=$(HOME)/lib/agda \
	  Main.agda
	-@echo '*** ALL TESTS OK ***'

clean:
	rm -rf crumbs

clobber: clean
	rm -rf deps
