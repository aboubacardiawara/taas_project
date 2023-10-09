# Define color codes
GREEN := \033[0;32m
RED := \033[0;31m
NC := \033[0m # No Color

all: clean test run

clean:
	@echo "$(GREEN)Cleaning project$(NC)"
	@dune clean

test:
	@echo "$(GREEN)Running test$(NC)"
	@dune test

run:
	@echo "$(GREEN)Running project$(NC)"
	@dune exec typeur_evaluateur
