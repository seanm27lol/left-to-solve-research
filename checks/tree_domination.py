import itertools

def canonical_key(adj):
    def tree(v,parent):
        return '('+''.join(sorted(tree(w,v) for w in adj[v] if w!=parent))+')'
    return min(tree(v,-1) for v in range(len(adj)))

def extend(trees):
    fresh={}
    for adj in trees:
        n=len(adj)
        for v in range(n):
            neigh=[w.copy() for w in adj]+[[v]]
            neigh[v].append(n)
            fresh[canonical_key(neigh)]=neigh
    return list(fresh.values())

def invariants(adj):
    n=len(adj)
    neighborhoods=[sum(1<<w for w in N) for N in adj]
    edges=[(v,w) for v,N in enumerate(adj) for w in N if v<w]
    gamma=tau=n
    for mask in range(1,1<<n):
        size=mask.bit_count()
        if size<gamma and all(N&mask for N in neighborhoods):
            gamma=size
        if size<tau and all(mask & ((1<<v)|(1<<w)) for v,w in edges):
            tau=size
    for deletions in range(n):
        for missing in itertools.combinations(edges,deletions):
            degrees=list(map(len,adj))
            for u,v in missing:
                degrees[u]-=1
                degrees[v]-=1
            if max(degrees)<=2:
                return gamma,1+deletions,tau

count=tight=0
trees=[[[]]]
for n in range(2,12):
    trees=extend(trees)
    for T in trees:
        gamma,p,tau=invariants(T)
        assert tau <= gamma+max(0,p-2)
        count+=1
        tight+=p>=2 and tau==gamma+p-2
print(count,tight)
