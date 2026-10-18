"""Standard input of `bench/parse`: 4,000,000 signed decimal numbers, one per line, from a 64-bit
LCG."""
import sys

x = 12345
out = []
for _ in range(4000000):
    x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
    out.append(str((x >> 33) % 2000001 - 1000000))
sys.stdout.write("\n".join(out) + "\n")
