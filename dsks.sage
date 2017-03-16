import hashlib, binascii
from collections import defaultdict

class TooManyAttemptsException(Exception):
    pass

def hash_as_integer(message):
    digest = hashlib.sha1(message).hexdigest() 
    return int(digest, 16)

def is_primitive_root(g, p, factors):
    """
    checks if g^((p-1)/q) != 1 mod p for every factor q of p-1. The factors
    should be provided by the factor parameter. Returns true if g is a primitive
    root mod p.
    """
    for q in factors:
        if power_mod(int(g), int((p-1)/q), p) == 1:
            return False
    return True

class RSAKeyPair:

    def __init__(self, bitsize):
        bitsize = bitsize/2
        for _ in range(100):
            p = random_prime(2^bitsize, lbound=2^(bitsize-1)) 
            q = random_prime(2^bitsize, lbound=2^(bitsize-1)) 
            if len((p*q).bits()) == 2*bitsize:
                self.N = p*q
                self.e = 65537
                self.d = inverse_mod(self.e, lcm(p-1, q-1))
                return
        raise TooManyAttemptsException("failed to generate a rsa modulus of exact bitsize")

    def sign(self, message):
        hai = hash_as_integer(message)
        #no padding ftw
        return pow(hai, self.d, self.N)

    def verify(self, message, sig):
        hai = hash_as_integer(message)
        #no padding ftw again
        return pow(sig, self.e, self.N) == hai

    def generate_bad_params(self, message, signature, max_subgroup_size=16, max_attempts=2000):
        all_primes = list(primes(2^max_subgroup_size))
        for _ in range(1,max_attempts):  # lets limit the number of times we try this
            shuffle(all_primes)
            try:
                p, p_factors, remaining_primes = self.generate_bad_params_helper(len(self.N.bits())/2, message, copy(all_primes), signature, max_subgroup_size, max_attempts)
                if not is_primitive_root(message, p, p_factors) or not is_primitive_root(signature, p, p_factors):
                    continue
                q, q_factors, _ = self.generate_bad_params_helper(len(self.N.bits())/2, message, remaining_primes, signature, max_subgroup_size, max_attempts)
                if not is_primitive_root(message, q, q_factors) or not is_primitive_root(signature, q, q_factors):
                    continue
                if not self.N < p*q:
                    continue
                return p,q
            except TooManyAttemptsException:
                continue
        raise TooManyAttemptsException("failed to generate a malicious p and q")
        
    def generate_bad_params_helper(self, bitsize, padded_message, all_primes, signature, max_subgroup_size=16, max_attempts=100):
        p_factors = []
        p = 2

        # multiply random small primes until we cross a threshold
        while len(p.bits()) < bitsize-max_subgroup_size:
            c = all_primes.pop()
            p_factors.append(c)
            p *= c

        # multiply random primes until we get an exact bitsize match where p+1 is prime
        for _ in range(1,max_attempts):
            c = all_primes.pop()
            option = (p*c)+1
            if len(option.bits()) == bitsize and option.is_prime():
                p_factors.append(c)
                p = option
                return p, p_factors, all_primes
            else:
                all_primes.insert(0, c)
        raise TooManyAttemptsException("failed to generate a evil prime of correct bitsize")


    def small_factors(num, bound=2^20):
        """
        small_factors returns a Factorization of num of all primes smaller than
        bound.
        """
        factors = defaultdict(int)
        p = 2
        while num > 1 and p < bound:
            if num % p == 0: 
                factors[p] += 1
                num /= p
            else:
                p = next_prime(p)
        return Factorization(factors.items())


class ECDSAKeyPair:

    def __init__(self, E, g):
        """
        returns (d, Q) where Q = d*G
        """
        # setup curve and field
        self.E = E
        self.F = E.base_field()
        self.G = g
        self.N = g.order() 
        
        # generate keypair
        d = randint(1, self.N)
        q = d*self.G
        self.d = d
        self.Q = q

    def sign(self, message):
        """
        Given a string, sign returns the signature pair (r,s)
        """
        k = randint(1, self.N)
        r,_ = (k*self.G).xy(); r = int(r) #sets r to the x coord of kG
        hai = hash_as_integer(message)
        kinv = inverse_mod(k, self.N)
        s = ((hai + self.d * r) * kinv) % self.N
        return (r,s) 

    def verify(self, message, r, s):
        """
        Given a string and a signature (r,s), verify returns True if the
        signature is valid and False otherwise.
        """
        hai = hash_as_integer(message)
        w = inverse_mod(s, self.N)
        u1 = (hai * w) % self.N
        u2 = (r * w) % self.N
        P1 = u1*self.G
        P2 = u2*self.Q 
        R,_ = (P1+P2).xy()
        return r == int(R)

    def create_valid_keypair(self, message, r, s):
        """
        creates a valid keypair for a particular message/signature pair. 
        only requires the original public key, and the target
        message/signature pair.
        returns a new ECDSAKeyPair that will succeed signature verification.
        """
        hai = hash_as_integer(message)
        w = inverse_mod(s, self.N)
        u1 = (hai * w) % self.N
        u2 = (r * w) % self.N
        R = u1*self.G + u2*self.Q
        dp = randint(1, self.N)
        t = u1 + u2*dp
        Gp = inverse_mod(t, self.N) * R
        Qp = dp * Gp
        kp = ECDSAKeyPair(self.E, Gp)    
        kp.Q = Qp
        kp.d = dp
        return kp


def test():
    for _ in range(100):
        #test ecdsa dsks
        F = FiniteField(233970423115425145524320034830162017933)
        E = EllipticCurve(F, [-95051,11279326])
        g = E(182, 85518893674295321206118380980485522083)
        kp = ECDSAKeyPair(E, g)
        r,s = kp.sign("allo")
        assert kp.verify("allo", r,s)
        assert not kp.verify("hello", r,s)
        kpp = kp.create_valid_keypair("allo", r,s) 
        assert kpp.verify("allo", r,s)

        #test rsa
        rkp = RSAKeyPair(256)
        s = rkp.sign("allooooo") 
        assert rkp.verify("allooooo", s)
        assert not rkp.verify("helloooooo", s)

#if __name__ == "__main__":
    #test()
