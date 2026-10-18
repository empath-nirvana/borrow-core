"""Standard input of `bench/wordcount`: 3,000,000 words, ten to a line, drawn by a 64-bit LCG
from about 4000 distinct words, the common ones far more often (a Zipf-like law)."""
import sys

WORDS = ("the of and to in a is that for it as was with be by on not he this are or his from at "
         "which but have an they you were her she there one all we their been has would when "
         "who will more no if out so said what up its about than into them can only other new "
         "some could time these two may then do first any my now such like our over man me even "
         "most made after also did many before must through back years where much your way well "
         "down should because each just those people how too little state good very make world "
         "still own see men work long get here between both life being under never day same "
         "another know while last might us great old year off come since against go came right "
         "used take three").split()

x = 7
out = []
for i in range(3000000):
    x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
    k = int((((x >> 33) % 1000003) / 1000003.0) ** 3 * 4000)
    out.append(WORDS[k % len(WORDS)] + ("" if k < len(WORDS) else str(k // len(WORDS))))
    out.append("\n" if i % 10 == 9 else " ")
sys.stdout.write("".join(out))
