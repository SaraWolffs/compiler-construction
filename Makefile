.PHONY: test

test :
	@idris -p contrib RunTests.idr -o test
	@./test
	@rm test
