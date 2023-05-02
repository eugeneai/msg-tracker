.PHONY: test erase-db serv

test:
	curl -X PUT -d @data/msg-test.txt http://localhost:3333/api-1.0/messages/

serv:
	cabal run

erase-db:
	rm -rf /var/tmp/*.{kct,kch}
