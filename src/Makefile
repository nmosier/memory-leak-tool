LLS = $(basename $(wildcard ../tests/test*.ll))
TESTS = $(LLS:.ll=)

.PHONY: test
test: $(TESTS)
	echo $(TESTS)

.PHONY: FORCE
FORCE:

../tests/test%.ll: FORCE
	$(MAKE) -C ../tests $(@:../tests/%=%)

test%: ../tests/test%.ll
	./main.py $<
