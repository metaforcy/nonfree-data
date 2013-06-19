
.PHONY: bundle

NONFREE_DIR=nonfree-data
EXAMPLE_THYS={FSets_Bags.thy,FSets_Alternatives.thy,Algebra.thy,Prelim.thy,Terms_with_Bindings.thy}
ZIPPED_FILES=$(NONFREE_DIR)/*.thy $(NONFREE_DIR)/ex/$(EXAMPLE_THYS) $(NONFREE_DIR)/*.ML $(NONFREE_DIR)/*.el $(NONFREE_DIR)/README metarec/*.ML metarec/*.thy

bundle:
	cd .. &&   rm -f $(NONFREE_DIR)/bundle.zip &&   zip $(NONFREE_DIR)/bundle.zip $(ZIPPED_FILES) &&   cd $(NONFREE_DIR)

