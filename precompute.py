# Size: 39
SEQ_256 = [1, 2, 5, 6, 8, 9, 13, 15, 20, 21, 25, 27, 31, 32, 37, 44, 45, 46, 51, 57, 70, 72, 73, 94, 103, 104, 114, 132, 149, 151, 159, 171, 178, 185, 189, 196, 205, 233, 247]

# Size: 13
SEQ_64 = [1, 2, 4, 5, 11, 13, 19, 25, 28, 29, 30, 32, 33]

def generate_powers(seq, additional):

    assert set(seq).isdisjoint(set(additional))
    full_seq = list(sorted(seq + additional))

    for (j, elem) in enumerate(seq):
        if elem == 1:
            print(f"x[{j+1}] = x")
            continue

        subseq = full_seq[:full_seq.index(elem)]
        for x in subseq:
            try:
                idx1 = seq.index(x)
                idx1_str = f"{idx1+1}"
            except ValueError:
                idx1_str = f"temp_{x}"

            y = elem - x

            if y in subseq:
                try:
                    idx2 = seq.index(y)
                    idx2_str = f"{idx2+1}"
                except ValueError:
                    idx2_str = f"temp_{y}"

                print(f"x[{j+1}] = {idx1_str} * {idx2_str} // contains {elem}")
                break
        else:
            print(elem, "!!!")


def generate_window(seq, N):
    seq = [0] + seq

    res = []
    for x in range(N):
        if x in seq:
            res.append([seq.index(x) + 1, 0])
            continue

        for y in seq:
            if x - y in seq:
                res.append([seq.index(y) + 1, seq.index(x - y) + 1])
                break

    print(res)


if __name__ == '__main__':
    #generate_powers(SEQ_64, [3, 6, 10])
    #generate_window(SEQ_64, 64)

    #generate_powers(SEQ_256, [3, 7, 18])

    ops_ref = lambda w, b: 2**w + b / w + b
    ops_test = lambda w, k, b: k + (b / w) * (k + 2 * (2**w - k)) / 2**w + b

    print(ops_ref(4, 1024))
    print(ops_test(6, 13, 1024))
    print(ops_test(8, 90, 1024))



