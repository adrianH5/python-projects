import re


def add_tok(train_sentences, train_labels, tokenizer, tokenizer_file):
    _new_tokens = []
    for i in range(len(train_sentences)):
        for j in range(len(train_sentences[i])):
            if train_labels[i][j]:
                _new_tokens.append(train_sentences[i][j])

    new_tokens = []
    for token in _new_tokens:
        delimiters = [" ", "-", "/", "(", ")", ".", "_", "[", "]"]
        flag = False
        for i in delimiters:
            if i in token:
                flag = True
        if flag:
            pattern = "|".join(map(re.escape, delimiters))
            tokens_ = [x for x in re.split(pattern, token) if x]
            new_tokens.extend(tokens_)
        else:
            new_tokens.append(token)

    _new_tokens_ = []
    for i in new_tokens:
        match = re.match(r"^[A-Za-z]+", i)
        if match:
            match = match.group()
            _new_tokens_.append(match)

    _new_tokens_ = list(set(_new_tokens_))
    # print(_new_tokens_)
    # print(len(_new_tokens_))
    # exit()
    num_added_tokens = tokenizer.add_tokens(_new_tokens_)
    tokenizer.save_pretrained(tokenizer_file)
    print("---------------------------------------------")
    print(f"Number of tokens added: {num_added_tokens}")
