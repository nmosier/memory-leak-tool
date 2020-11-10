.PHONY: test
test:
	./block.py ../tests/test3.ll

../tests/test%.ll:
	$(MAKE) -C ../tests $(@:../tests/%=%)

test%: ../tests/test%.ll
	./block.py $<
