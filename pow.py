import random


def bit(x, pos):
    return (x >> pos) & 1 == 1


def square(x):
    return mul(x, x)


def mul(x, y):
    return x + y


def pow_sliding_window(x, exponent):

    WINDOW = 4
    WINDOW_MASK = (1 << (WINDOW - 1)) - 1

    m = exponent.bit_length() - 1

    powers = [None] * 2**(WINDOW - 1)

    x_start = x
    for i in range(WINDOW-1):
        x_start = square(x_start)
    # x_start = x^(2^(WINDOW-1))

    powers[0] = x_start
    for i in range(1, 2**(WINDOW-1)):
        powers[i] = mul(powers[i-1], x)

    Q = 0
    i = m
    while True:
        #print(f"i = {i}, Q = {Q}")
        if not bit(exponent, i):
            #print("- bit=0, doubling")
            Q = square(Q)
            if i == 0:
                break
            i -= 1
        else:
            if i < WINDOW - 1:
                mask = 2**(i+1)-1
                small_power = exponent & mask
                #print(f"- final part; remainder = {small_power}")
                for j in reversed(range(small_power.bit_length())):
                    Q = square(Q)
                    if bit(small_power, j):
                        Q = mul(Q, x)
                break

            else:
                t = (exponent >> (i - WINDOW + 1)) & WINDOW_MASK
                #print(f"- full window, t={t}")
                for j in range(WINDOW):
                    Q = square(Q)
                Q = mul(Q, powers[t])
                if i == WINDOW - 1:
                    break
                else:
                    i -= WINDOW

    return Q


def is_prime(n):
    if n in (1, 2):
        return True
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


def decompose(pwr, window, always_decompose=False):
    primes = []
    for i in range(1, 2**window):
        if is_prime(i):
            primes.append(i)

    prev_prime = []
    for i in range(1, 2**window):
        #print("i =", i)
        for j in reversed(range(len(primes))):
            if i >= primes[j]:
                #print("i >= prime", primes[j])
                prev_prime.append(j)
                break

    prev_prime_idx = prev_prime[pwr-1]
    if not always_decompose or pwr == 1:
        if primes[prev_prime_idx] == pwr:
            return pwr,

    for j in reversed(range(prev_prime_idx+1)):
        p1 = primes[j]
        p2 = pwr - p1
        pidx = prev_prime[p2-1]
        if primes[pidx] == p2:
            return p1, p2

    if pwr % 2 == 1:
        if always_decompose and primes[prev_prime_idx] == pwr:
            prev_prime = primes[prev_prime_idx-1]
        else:
            prev_prime = primes[prev_prime_idx]
        p1, p2 = decompose(pwr - prev_prime, window)
        return prev_prime, p1, p2

    raise Exception(pwr)


def pow_primes(x, exponent):
    WINDOW = 8

    primes = []
    for i in range(1, 2**WINDOW):
        if is_prime(i):
            primes.append(i)

    prev_prime = []
    for i in range(1, 2**WINDOW):
        #print("i =", i)
        for j in reversed(range(len(primes))):
            if i >= primes[j]:
                #print("i >= prime", primes[j])
                prev_prime.append(j)
                break

    print(primes)
    print(prev_prime)

    bits = exponent.bit_length()
    num_windows = (bits - 1) // WINDOW + 1

    for i in reversed(range(num_windows)):
        pwr = (exponent >> (i * WINDOW)) & (2**WINDOW-1)

        print("pwr = ", pwr)

        if pwr == 0:
            pass
        elif pwr % 2 == 1:
            prev_prime_idx = prev_prime[pwr-1]
            if primes[prev_prime_idx] == pwr:
                print(f"Odd {pwr} is a prime")
                continue

            for j in reversed(range(prev_prime_idx+1)):
                p1 = primes[j]
                p2 = pwr - p1
                pidx = prev_prime[p2-1]
                if primes[pidx] == p2:
                    print(f"Odd {pwr} decomposed into", p1, p2)
                    break

        else:
            prev_prime_idx = prev_prime[pwr-1]
            if primes[prev_prime_idx] == pwr:
                print(f"Even {pwr} is a prime")
                continue

            for j in reversed(range(prev_prime_idx+1)):
                p1 = primes[j]
                p2 = pwr - p1
                pidx = prev_prime[p2-1]
                if primes[pidx] == p2:
                    print(f"Even {pwr} decomposed into", p1, p2)
                    break


def print_precompute(w):

    primes = []
    for i in range(1, 2**w):
        if is_prime(i):
            primes.append(i)

    lst = []
    for i in range(1, 2**w):
        if is_prime(i):
            pos = primes.index(i)
            comps = decompose(i, w, True)
            js = [primes.index(j) + 1 for j in comps] + [0] * (3 - len(comps))
            lst.append(js)
            #print(pos, js, i)

    print("[" + ",".join(repr(l) for l in lst) + "]")


def print_precompute2(w):

    primes = []
    for i in range(1, 2**w):
        if is_prime(i):
            primes.append(i)

    lst = []
    for i in range(1, 2**w):
        comps = decompose(i, w)
        js = [primes.index(j) + 2 for j in comps] + [0] * (3 - len(comps))
        lst.append(js)
        #print(i, js)

    print("[" + ",".join(repr(l) for l in lst) + "]")


if __name__ == '__main__':
    x = 2

    #pow_primes(2, 125714951324958123945)

    print_precompute(6)
    print_precompute2(6)

    print(minimal_set(20))

    """
    for i in range(1, 1000):
        print("-"*80)
        e = i
        print(e)
        ref = x*e
        test = pow_sliding_window(x, e)
        assert ref == test
    """


