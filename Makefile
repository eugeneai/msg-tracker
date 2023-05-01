.PHONY: test








test:
	curl -X PUT -d @data/msg-test.txt http://localhost:3333/api-1.0/messages/
