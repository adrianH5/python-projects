.PHONY: dev test ci clean clean-docker

dev:
	docker-compose -f docker-compose.yml -f docker-compose.dev.yml up --build

test:
	docker-compose -f docker-compose.yml -f docker-compose.dev.yml run --rm api pytest -q

ci:
	docker-compose -f docker-compose.yml -f docker-compose.ci.yml up -d
	docker-compose -f docker-compose.yml -f docker-compose.ci.yml run --rm api tracelab cli replay specs/*.yml

clean:
	docker-compose -f docker-compose.yml -f docker-compose.dev.yml -f docker-compose.ci.yml down -v --remove-orphans

clean-docker:
	docker builder prune --all --force
