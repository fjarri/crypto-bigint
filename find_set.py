from itertools import combinations


def score(s, n):
    res = 0
    for i in range(1, n):
        if i in s:
            res += 1
            continue
        for j in s:
            if i - j in s:
                res += 2
                break
        else:
            return None
    return res


def find_set(n):
    for set_len in range(1, n):
        min_score = 1e9
        best_sets = []
        for s in combinations(list(range(1, n)), set_len):
            x = score(s, n)
            if x is not None:
                if x < min_score:
                    min_score = x
                    best_sets = [s]
                elif x == min_score:
                    best_sets.append(s)

        if len(best_sets) > 0:
            print(f"set len {set_len}, best sets ({len(best_sets)}) {best_sets} ({min_score})")
            #print(n, len(best_sets[0]))
            break


if __name__ == '__main__':
    find_set(16)
