"""Independent tests for the consecutive-cubefull C++ search."""
from pathlib import Path
from subprocess import check_output, run
from tempfile import TemporaryDirectory
import re


def full_flags(bound):
    """Eliminate exactly the two forbidden positive exponent classes at each prime."""
    prime = bytearray([1]) * (bound + 1)
    prime[:2] = bytes(2)
    good = bytearray([1]) * (bound + 1)
    good[0] = 0
    for p in range(2, bound + 1):
        if not prime[p]:
            continue
        prime[2*p::p] = bytes(bound//p - 1)
        for d in range(p, bound + 1, p):
            if d % (p*p*p):
                good[d] = 0
    return good


def full_list_by_normal_form(bound):
    """Enumerate a deliberately noncanonical superset of triples a,b,c and deduplicate."""
    terms = set()
    c = 1
    while c**5 <= bound:
        b = 1
        while b**4 * c**5 <= bound:
            scale = b**4*c**5
            a = 1
            while (v := a**3*scale) <= bound:
                terms.add(v)
                a += 1
            b += 1
        c += 1
    return sorted(terms)


def counts(terms, limit):
    terms_set = set(terms)
    return (len(terms), sum(v%2==0 for v in terms),
            sum(1 for v in terms if (v%8 == 1 and v != 1) or (v%8 == 7 and v+1 <= limit)),
            sum(v+1 in terms_set for v in terms if v <= limit))


def main():
    source = Path(__file__).with_name('consecutive_cubefull.cpp')
    with TemporaryDirectory() as tmp:
        exe = Path(tmp)/'check'
        run(['g++','-O3','-std=c++17',str(source),'-o',str(exe)],check=True)
        for k in (3,5,6,12,15):
            limit = 10**k
            vals = full_list_by_normal_form(limit+1)
            if k <= 6:
                flags = full_flags(limit+1)
                assert vals == [v for v in range(1,limit+2) if flags[v]]
            got = check_output([str(exe), str(k)],text=True)
            stats = re.search(r': (\d+); even terms (\d+); odd anchors (\d+); filtered even terms \d+; consecutive pairs (\d+)',got)
            assert stats and tuple(map(int,stats.groups())) == counts(vals,limit)
            print(k, counts(vals,limit))

        # Inject two synthetic odd endpoints into the enumeration solely as a
        # positive control. Both must be seen on either side of the real 64.
        altered = Path(tmp)/'injected.cpp'
        insertion = 'auto families = make_families(limit+1);'
        cpp = source.read_text()
        assert cpp.count(insertion) == 1
        altered.write_text(cpp.replace(insertion, insertion+
            '\n    families.push_back({63,1}); families.push_back({65,1});'))
        run(['g++','-O3','-std=c++17',str(altered),'-o',str(exe)],check=True)
        control = run([str(exe), '3'],text=True,capture_output=True)
        assert control.returncode == 1
        assert sorted(x for x in control.stdout.splitlines() if x.startswith('pair ')) == [
            'pair 63 64', 'pair 64 65']
        print('Both injected orientations recovered by exact comparison.')


if __name__ == '__main__':
    main()
