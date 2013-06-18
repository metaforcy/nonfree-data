
.PHONY: bundle

NONFREE_DIR=nonfree-data
ZIPPED_FILES=$(NONFREE_DIR)/*.thy $(NONFREE_DIR)/*.ML $(NONFREE_DIR)/*.el $(NONFREE_DIR)/README metarec/*.ML metarec/*.thy

bundle:
	cd .. && zip $(NONFREE_DIR)/bundle.zip $(ZIPPED_FILES) && cd $(NONFREE_DIR)

