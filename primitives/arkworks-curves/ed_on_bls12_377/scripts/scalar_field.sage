modulus = 2111115437357092606062206234695386632838870926408408195193685246394721360383

assert(modulus.is_prime())

Fp = GF(modulus)

generator = Fp(0);
for i in range(0, 30):
    i = Fp(i);
    neg_i = Fp(-i)
    if not(i.is_primitive_root() or neg_i.is_primitive_root()):
        continue
    elif i.is_primitive_root():
        assert(i.is_primitive_root());
        print("Generator: %d" % i)
        generator = i
        break
    else:
        assert(neg_i.is_primitive_root());
        print("Generator: %d" % neg_i)
        generator = neg_i
        break


two_adicity = valuation(modulus - 1, 2);
trace = (modulus - 1) / 2**two_adicity;
two_adic_root_of_unity = generator^trace
print("2-adic Root of Unity: %d " % two_adic_root_of_unity)
