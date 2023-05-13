import numpy
import matplotlib.pyplot as plt

fig = plt.figure(figsize=(6.4*2, 4.8*2))
sp = fig.add_subplot(1, 1, 1)

bs = numpy.array([128, 256, 512, 1024, 2048])
ks = [6, 8, 15, 20, 40]
for w, k in zip((4, 5, 6, 7, 8), ks):
    ys1 = 2**w + bs / w
    ys2 = k + bs / w * ((k + 2 * (2**w - k)) / 2**w)

    sp.semilogx(bs, ys1, label=f"ref, w={w}")
    sp.semilogx(bs, ys2, label=f"sums, w={w}", linestyle=":")

sp.legend()

fig.savefig('ops.pdf')


fig = plt.figure(figsize=(6.4*2, 4.8*2))
sp = fig.add_subplot(1, 1, 1)

ks = numpy.arange(40, 256)
w = 8

for b in (256, 512, 1024, 2048):
    ys2 = ks + b / w * ((ks + 2 * (2**w - ks)) / 2**w)
    sp.plot(ks, ys2, label=f"b={b}")
    sp.legend()

fig.savefig('ops2.pdf')
