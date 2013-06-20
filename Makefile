
.PHONY: bundle

NONFREE_DIR=nonfree-data
ZIPPED_FILES=README $(NONFREE_DIR)/*.thy $(NONFREE_DIR)/Examples/*.thy $(NONFREE_DIR)/*.ML $(NONFREE_DIR)/*.el $(NONFREE_DIR)/README metarec/*.ML metarec/*.thy

bundle:
	cd .. &&   rm -f $(NONFREE_DIR)/bundle.zip &&   zip $(NONFREE_DIR)/bundle.zip $(ZIPPED_FILES) &&   cd $(NONFREE_DIR)

