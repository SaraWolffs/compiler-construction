.PHONY: test

test :
	@idris -p contrib -p pruviloj RunTests.idr -o test
	@./test
	@rm test
