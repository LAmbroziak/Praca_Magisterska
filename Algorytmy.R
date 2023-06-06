library(microbenchmark)
library(dplyr)
library(ClusterR)
library(SimDesign)

{
  #k-ta wartosc z listy l
  get = function(l, k) {
    return(l[[k]])
  }
  
  # fumkcja dziala jak funkcja diag, ale gdy argumentem jest liczba, to nie tworzy macierzy o takim rozmiarze, tylko zwraca ta liczbe
  diag2 = function(M) {
    if (length(M) > 1)
      return(diag(M))
    else
      return(matrix(M, nrow = 1))
  }
  
  # Losowanie macierzy 0-1 podajac macierz prawdopodobinstw
  los = function(P) {
    n = nrow(P)
    return(matrix(rbinom(n ^ 2, 1, P), ncol = n))
  }
  
  # Losowanie wielu macierzy 0-1 podajac liste macierzy prawdopodobinstw
  mlos = function(P) {
    m = length(P)
    L = list()
    for (i in 1:m) {
      L[i] = list(los(P[[i]]))
    }
    return(L)
  }
  
  # Generowanie macierzy niesymetrycznych wymiaru n na n
  runi = function(n) {
    return(matrix(round(runif(n ^ 2, 0, 1), 2), ncol = n))
  }
  
  # generowanie oronormalnej macierzy wymiaru n
  gen.ort = function(n) {
    return(svd(los(matrix(rep(
      0.5, n
    ), ncol = 1)))[[2]])
    
  }
  
  # Generowanie macierzy przynaleznoœci dla n wierzcholkow o K klasach
  gen.Z = function(n, K) {
    q = n / K
    Z = matrix(rep(0, n * K), ncol = K)
    for (i in (0:(K - 1))) {
      Z[(i * q + 1):((i + 1) * q), i + 1] = 1
    }
    return(Z)
  }
  
  # Genruje macierze prawdopodobieñstw dla listy macierzy punktacji i macierzy V
  gen.p = function(R, V) {
    m = length(R)
    L = list()
    for (i in 1:m) {
      L[i] = list(V %*% R[[i]] %*% t(V))
    }
    return(L)
  }
  
  # Genruje liste n takich samych macierzy prawdopodobieñstw dla danej macierzy punktacji i macierzy V
  gen.pn = function(R, V, n) {
    L = list()
    L[c(1:n)] = list(V %*% R %*% t(V))
    return(L)
  }
  
  #Genruje macierze prawdopodobieñstw dla listy macierzy punktacji i macierzy V oraz U; P=V R U^T
  gen.p2 = function(R, V, U) {
    m = length(R)
    L = list()
    for (i in 1:m) {
      L[i] = list(V %*% R[[i]] %*% t(U))
    }
    return(L)
  }
  
  #Genruje listy macierzy punktacji
  gen.R = function(m, n) {
    l = list()
    for (i in 1:m) {
      l[i] = list(runi(n))
    }
    return(l)
  }
  
  # Generowanie listy macierzy sasiedztwa
  gen.lista = function(n, K, m) {
    R = list()
    for (i in 1:m) {
      R[i] = list(runi(K))
    }
    P = gen.p(R, gen.Z(n, K))
    return(mlos(P))
  }
  
  #mieszanie wierszy macierzy
  tas = function(M) {
    n = dim(M)[1]
    for (i in 1:n) {
      M[i, ] = sample(M[i, ])
    }
    return(M)
  }
  
  # Sprawdzanie czy wartosc jest NA i zamienia na 0
  isna = function(x) {
    if (is.na(x))
      return (0)
    else
      return (x)
  }
  
  #obliczanie macierzy D potrzebnej w utworzeniu Laplasianu lub jego zregualryzowanej wersji
  Lap = function(A, tau = 0) {
    n = dim(A)[1]
    D = matrix(data = 0,
               nrow = n,
               ncol = n)
    for (i in 1:n) {
      D[i, i] = 1 / sqrt(sum(A[, i]) + sum(A[i, ]) - A[i, i] + tau)
    }
    return(D)
  }
  
  #obliczanie spectralnego zanuzenia Laplacea,lub jego zregularyzowana wersje
  LSE = function(A, tau = 0) {
    D = Lap(A, tau)
    n = dim(A)[1]
    L = D %*% A %*% D
    U = svd(L)
    s = diag2(sqrt(U[[1]]))
    l = list(U[[2]] %*% s)
    l[2] = U[1]
    return(l)
  }
  
  # Algorytm MASE w ktorym krok ASE zastapiono LSE
  MLSE = function(G, tau = 0, q = 0) {
    m = length(G)
    M = list()
    R = list()
    d = rep(0, m)
    for (i in 0:(m - 1)) {
      M[c(2 * i + 1, 2 * i + 2)] = LSE(G[[i + 1]], tau)
      d[i + 1] = Emb.dim(M[[2 * i + 2]])[[2]]
    }
    n = nrow(G[[1]])
    U = matrix(nrow = n, ncol = 0)
    for (i in 0:(m - 1)) {
      U = matrix(c(U, (M[[2 * i + 1]][, 1:d[i + 1]])), nrow = n)
    }
    Q = svd(U)
    if (q <= 0) {
      D = Emb.dim(Q[[1]])[[2]]
    }
    else
    {
      D =  min(q, dim(Q[[2]])[2])
    }
    V = matrix(Q[[2]][, 1:D], ncol = D)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% V)
    }
    R[m + 1] = list(V)
    return(R)
  }
  
  #Algorytm ASE dla sredniej z macierzy sasiedztwa
  ASE.Mean = function(G, q = 0) {
    m = length(G)
    R = list()
    A = G[[1]]
    if (m > 1) {
      for (i in 2:m) {
        A = A + G[[i]]
      }
    }
    A = A / m
    S = svd(A)
    if (q <= 0)
    {
      d = Emb.dim(S[[1]])[[2]]
    }
    else
    {
      d = q
    }
    V = matrix(S[[2]][, 1:d], ncol = d)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% V)
    }
    R[m + 1] = list(V)
    return(R)
  }
  
  # Algorytm ASE dla listy macierzy sasiedztwa
  ASE.list = function(G, q = 0) {
    m = length(G)
    P = list()
    for (i in 1:m) {
      S = svd(G[[i]])
      if (q <= 0)
      {
        d = Emb.dim(S[[1]])[[2]]
      }
      else
      {
        d = min(q, dim(S[[2]])[2])
      }
      V = matrix(S[[2]][, 1:d], ncol = d)
      P[i] = list(V %*% t(V) %*% G[[i]] %*% V %*% t(V))
    }
    return(P)
  }
  
  # Wyznaczanie wymiaru zanuzenia z uzyciem rozkladu normalnego
  Emb.dim = function(t) {
    s = round(t, 8)
    s = s[s > 0]
    n = length(s)
    mu1 = rep(0, n)
    mu2 = rep(0, n)
    sig1 = rep(0, n)
    sig2 = rep(0, n)
    l = rep(0, n)
    for (i in 1:n - 1) {
      l1 = s[1:i]
      l2 = s[(i + 1):n]
      mu1[i] = mean(l1)
      mu2[i] = mean(l2)
      sig1[i] =  isna(var(l1))
      sig2[i] =  isna(var(l2))
      l[i] = sum(log(dnorm(l1, mu1[i], sqrt(sig1[i])))) + sum(log(dnorm(l2, mu2[i], sqrt(sig2[i]))))
    }
    l[1] = sum(log(dnorm(s[-1], mu2[1], sqrt(sig2[1]))))
    l[n - 1] = sum(log(dnorm(s[-n], mu1[n - 1], sqrt(sig1[n - 1]))))
    l[n] = sum(log(dnorm(s, mean(s), sqrt(var(s)/2))))
    q = which.max(l)
    return(list(l, q))
    
  }
  
  # Wyznaczanie wymiaru zanuzenia z uzyciem rozkladu jednostajnego
  Emb.dim.uni = function(t) {
    s = round(t, 8)
    s = s[s > 0]
    n = length(s)
    mu1 = rep(0, n)
    mu2 = rep(0, n)
    sig = rep(0, n)
    l = rep(0, n)
    for (i in 2:n - 2) {
      l1 = s[1:i]
      l2 = s[(i + 1):n]
      mu1[i] = 1 / (max(l1) - min(l1))
      mu2[i] = 1 / (max(l2) - min(l2))
      
      l[i] =  i * log(mu1[i]) + (n - i) * log(mu2[i])
    }
    l[n - 1] = (n - 1) * log(1 / (max(s[-n]) - min(s[-n])))
    l[n] = n * log(1 / (max(s) - min(s)))
    l[1] = (n - 1) * log(1 / (max(s[-1]) - min(s[-1])))
    q = which.max(l)
    return(list(l, q))
    
  }
  
  # Rysowanie wykresu log-wiarogodnosci
  Emb.plot = function(E) {
    m = length(E[[1]])
    c = rep("black", m)
    c[E[[2]]] = "red"
    plot(
      E[[1]],
      main = "Profilowana log-wiarogodnoœæ",
      ylab = "",
      xlab = "Wymiar",
      type = "o",
      lwd = 3.5,
      col = c,
      pch = 16,
      cex = 1.3
    )
    abline(v = E[[2]], col = "grey", lty = 2)
  }
  
  # Algorytm MASE nieskalowany
  MASE_unscaled = function(G, q = 0) {
    m = length(G)
    M = list()
    R = list()
    d = rep(0, m)
    for (i in 0:(m - 1)) {
      M[c(2 * i + 1, 2 * i + 2)] = svd(G[[i + 1]])[c(1, 2)]
      d[i + 1] = Emb.dim(M[[2 * i + 1]])[[2]]
    }
    n = nrow(G[[1]])
    U = matrix(nrow = n, ncol = 0)
    for (i in 0:(m - 1)) {
      U = matrix(c(U, M[[2 * i + 2]][, 1:d[i + 1]]), nrow = n)
    }
    Q = svd(U)
    if (q <= 0)
    {
      D = Emb.dim(Q[[1]])[[2]]
    }
    else
    {
      D = min(q,dim(Q)[2])
    }
    V = matrix(Q[[2]][, 1:D], ncol = D)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% V)
    }
    R[m + 1] = list(V)
    return(R)
  }
  
  # Algorytm MASE skalowany z uzyciem rozkladow normalnych
  MASE = function(G, dim = 0) {
    m = length(G)
    M = list()
    R = list()
    d = rep(0, m)
    for (i in 0:(m - 1)) {
      M[c(2 * i + 1, 2 * i + 2)] = svd(G[[i + 1]])[c(1, 2)]
      if (dim <= 0) {
        d[i + 1] = Emb.dim(M[[2 * i + 1]])[[2]]
      }
      else
      {
        d[i + 1] = min(dim, Emb.dim(M[[2 * i + 1]])[[2]])
      }
    }
    n = nrow(G[[1]])
    U = matrix(nrow = n, ncol = 0)
    for (i in 0:(m - 1)) {
      U = matrix(c(U, (M[[2 * i + 2]][, 1:d[i + 1]]) %*% diag2(sqrt((
        M[[2 * i + 1]][1:d[i + 1]]
      )))), nrow = n)
    }
    Q = svd(U)
    if (dim <= 0) {
      D = Emb.dim(Q[[1]])[[2]]
    }
    else
    {
      D = min(dim, dim(Q[[2]])[2])
    }
    V = matrix(Q[[2]][, 1:D], ncol = D)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% V)
    }
    R[m + 1] = list(V)
    return(R)
  }
  
  # Algorytm MASE skalowany z uzyciem rozkladow jednostajnych
  MASE_uni = function(G, q = 0) {
    m = length(G)
    M = list()
    R = list()
    d = rep(0, m)
    for (i in 0:(m - 1)) {
      M[c(2 * i + 1, 2 * i + 2)] = svd(G[[i + 1]])[c(1, 2)]
      d[i + 1] = Emb.dim.uni(M[[2 * i + 1]])[[2]]
    }
    n = nrow(G[[1]])
    U = matrix(nrow = n, ncol = 0)
    for (i in 0:(m - 1)) {
      U = matrix(c(U, (M[[2 * i + 2]][, 1:d[i + 1]]) %*% diag2(sqrt((
        M[[2 * i + 1]][1:d[i + 1]]
      )))), nrow = n)
    }
    Q = svd(U)
    if (q <= 0)
    {
      D = Emb.dim.uni(Q[[1]])[[2]]
    }
    else
    {
      D = q
    }
    V = matrix(Q[[2]][, 1:D], ncol = D)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% V)
    }
    R[m + 1] = list(V)
    return(R)
  }
  
  # Algorytm MASE skalowany z uzyciem rozkladow normalnych dla przypadku P=VRU^T
  MASE_UV = function(G, q = 0) {
    m = length(G)
    M = list()
    R = list()
    d = rep(0, m)
    for (i in 0:(m - 1)) {
      M[c(3 * i + 1, 3 * i + 2, 3 * i + 3)] = svd(G[[i + 1]])
      d[i + 1] = Emb.dim(M[[3 * i + 1]])[[2]]
    }
    n = nrow(G[[1]])
    A = matrix(nrow = n, ncol = 0)
    B = matrix(nrow = n, ncol = 0)
    for (i in 0:(m - 1)) {
      A = matrix(c(A, (M[[3 * i + 2]][, 1:d[i + 1]]) %*% diag2(sqrt((
        M[[3 * i + 1]][1:d[i + 1]]
      )))), nrow = n)
      B = matrix(c(B, (M[[3 * i + 3]][, 1:d[i + 1]]) %*% diag2(sqrt((
        M[[3 * i + 1]][1:d[i + 1]]
      )))), nrow = n)
      
    }
    Q = svd(A)
    W = svd(B)
    if (q <= 0)
    {
      D = Emb.dim(Q[[1]])[[2]]
    }
    else
    {
      D = q
    }
    V = matrix(Q[[2]][, 1:D], ncol = D)
    U = matrix(W[[2]][, 1:D], ncol = D)
    for (i in 1:m) {
      R[i] = list(t(V) %*% G[[i]] %*% U)
    }
    R[m + 1] = list(V)
    R[m + 2] = list(U)
    return(R)
  }
  
  # Wyliczenie estymatorów P
  P_est = function(R) {
    l = list()
    n = length(R)
    for (i in 1:(n - 1)) {
      l[i] = list(R[[n]] %*% R[[i]] %*% t(R[[n]]))
    }
    return(l)
  }
  
  # Wyliczenie estymatorów P dla przypadku P=VRU^T
  P_est2 = function(R) {
    l = list()
    n = length(R)
    for (i in 1:(n - 2)) {
      l[i] = list(R[[n - 1]] %*% R[[i]] %*% t(R[[n]]))
    }
    return(l)
  }
  
  # znormalizowana odleglosc Frobeniusa miedzy macierzami
  Frob_dist = function(P, R) {
    return(norm(R - P, type = "F") / norm(P, type = "F"))
  }
  
  #  odleglosc Frobeniusa miedzy macierzami
  Frob = function(A,B){
  return(norm(A-B,type="F"))
}
  
  # odleglosc spektalna miedzy podprzestrzeniami
  Sub_dist = function(V, W) {
    return(norm(V %*% t(V) - W %*% t(W), type = "2"))
  }
  
  # Klasyfikator najblizszego sasiada z uzyciem odleglosci Frobeniusa
  Frob_class=function(Test,Train,LTest){
  m=length(Test)
  w=numeric(m)
  for (i in 1:m){
    Q=lapply(Train,FUN="Frob",B=Test[[i]])
    index=which.min(as.double(Q))
    w[i]=LTest[index]
  }
  return(w)
}
  
  #Obcina wartosci z macierzy do przedzialu [0,1]
  pm= function(M){
    n=nrow(M)
    return(matrix(apply(M,MARGIN=c(1,2),FUN=function(x){return(max(0,min(1,x)))}),nrow=n))
  }
 
  # Estymowanie rozk³adu ||R1-R2||_F przy Hipotezie 0 
  Boottest <- function(V, R, N = 200) {
  n = nrow(V)
  d = ncol(V)
  P = V %*% R %*% t(V) 
  bootstrap = sapply(1:N, function(i) {
    A1 = los(pm(P))
    A2 = los(pm(P))
    W = MASE(list(A1, A2),d)
    return(Frob(W[[1]],W[[2]]))
  })
  return(bootstrap)
}
  
  #Estymowanie p-wartosci
  pval <- function(test, null) {
    return(sapply(test, function(x) 
      sum(x <= null) / length(null)))
  }
  
  #Bootstrapowy test na rownosc dwoch macierzy punktacji
  test_COSIE <- function(V, R1, R2, N = 1000) {
  null1 = Boottest(V, R1,N)
  null2= Boottest(V, R2,N)
  test = Frob(R1 ,R2)
  p = max(pval(test, null1), pval(test, null2))
  return(list(p.value = p, null.dist1 = null1, null.dist2 = null2, 
              test = test))
  }
  
  # Estymowanie macierzy korelacji miedzy wspolrzednymi macierzy punktacji
  sig=function(P,V){
  n=nrow(V)
  d=ncol(V)
  S=matrix(0,d^2,d^2)
  for (k in 1:d){
    for (l in 1:d){
      for (kk in 1:d){
        for (ll in 1:d){
          S[k+d*(l-1),kk+d*(ll-1)]=t(V[,l]*V[,ll])%*% (P*(1-P)) %*% (V[,k]*V[,kk])
        }
      }
    }
  }
  return(S)
}
  
}

######################################################
##############         V         #####################
######################################################
{
  {
    Z = gen.Z(800, 20)
    R = gen.R(10,20)
    P = gen.p(R, Z)
    A = mlos(P)
    
    W = MASE_unscaled(A)
    W1 = MASE(A)
    W2 = MASE_uni(A)
    W3 = MASE_UV(A)
    W4 = MLSE(A)
    W5 = MLSE(A, 80)
    W6 = ASE.Mean(A)
    
    #rozklady jednostajne
    Emb.plot(Emb.dim.uni(svd(A[[4]])[[1]]))
    #tradycyjny
    Emb.plot(Emb.dim(svd(A[[2]])[[1]]))
    
    
    Vdok = Z %*% (diag2(1 / sqrt(diag(t(Z ) %*% Z))))
    
    Sub_dist(Vdok, W[[11]])
    Sub_dist(Vdok, W1[[11]])
    Sub_dist(Vdok, W2[[11]])
    Sub_dist(Vdok, W3[[11]])
    Sub_dist(Vdok, W4[[11]])
    Sub_dist(Vdok, W5[[11]])
    Sub_dist(Vdok, W6[[11]])
    Frob_dist(P[[1]], P_est(W)[[1]])
    Frob_dist(P[[1]], P_est(W1)[[1]])
    Frob_dist(P[[1]], P_est(W2)[[1]])
    Frob_dist(P[[1]], P_est2(W3)[[1]])
    Frob_dist(P[[1]], P_est(W4)[[1]])
    Frob_dist(P[[1]], P_est(W5)[[1]])
    Frob_dist(P[[1]], P_est(W6)[[1]])
  }
  {
    Z = gen.Z(500, 4)
    Vdok = Z %*% (diag2(1 / sqrt(diag(t(
      Z
    ) %*% Z))))
    R = gen.R(10,4)
    P = gen.p(R, Z)
    A = mlos(P)
    
    W = MASE_unscaled(A)
    W1 = MASE(A)
    W2 = MASE_uni(A)
    W3 = MASE_UV(A)
    W4 = MLSE(A)
    W5 = MLSE(A, 450)
    
    #rozklady jednostajne
    Emb.plot(Emb.dim.uni(svd(A[[4]])[[1]]))
    #tradycyjny
    Emb.plot(Emb.dim(svd(A[[2]])[[1]]))
    
    Sub_dist(Vdok, W[[11]])
    Sub_dist(Vdok, W1[[11]])
    Sub_dist(Vdok, W2[[11]])
    Sub_dist(Vdok, W3[[11]])
    Sub_dist(Vdok, W4[[11]])
    Sub_dist(Vdok, W5[[11]])
    
    Frob_dist(P[[1]], P_est(W)[[1]])
    Frob_dist(P[[1]], P_est(W1)[[1]])
    Frob_dist(P[[1]], P_est(W2)[[1]])
    Frob_dist(P[[1]], P_est2(W3)[[1]])
    Frob_dist(P[[1]], P_est(W4)[[1]])
    Frob_dist(P[[1]], P_est(W5)[[1]])
  }
  {
    Z = gen.Z(500, 1)
    Vdok = Z %*% (diag2(1 / sqrt(diag(t(
      Z
    ) %*% Z))))
    R = gen.R(10,1)
    P = gen.p(R, Z)
    A = mlos(P)
    
    W = MASE_unscaled(A)
    W1 = MASE(A)
    W2 = MASE_uni(A)
    W3 = MASE_UV(A)
    W4 = MLSE(A)
    W5 = MLSE(A, 90)
    
    #rozklady jednostajne
    Emb.plot(Emb.dim.uni(svd(A[[1]])[[1]]))
    #tradycyjny
    Emb.plot(Emb.dim(svd(A[[2]])[[1]]))
    
    Sub_dist(Vdok, W[[11]])
    Sub_dist(Vdok, W1[[11]])
    Sub_dist(Vdok, W2[[11]])
    Sub_dist(Vdok, W3[[11]])
    Sub_dist(Vdok, W4[[11]])
    Sub_dist(Vdok, W5[[11]])
    
    Frob_dist(P[[1]], P_est(W)[[1]])
    Frob_dist(P[[1]], P_est(W1)[[1]])
    Frob_dist(P[[1]], P_est(W2)[[1]])
    Frob_dist(P[[1]], P_est2(W3)[[1]])
    Frob_dist(P[[1]], P_est(W4)[[1]])
    Frob_dist(P[[1]], P_est(W5)[[1]])
  }
}
######################################################
###########         SUB DIST         #################
######################################################
# identyczne macierze prawdopodobienstw symertycze
{
B=matrix(data=c(0.4,0.1,0.1, 0.1,0.5,0.2, 0.1,0.2,0.6),nrow=3)
v=c(1,5,10,15,20,30,50,70,100)
M=50
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  P=gen.pn(B,Z,v[i])
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,0,3)
    W3=ASE.Mean(A,3)
    wyniki[1,i]=wyniki[1,i]+Sub_dist(Vdok,W[[v[i]+1]])
    wyniki[2,i]=wyniki[2,i]+Sub_dist(Vdok,W1[[v[i]+1]])
    wyniki[3,i]=wyniki[3,i]+Sub_dist(Vdok,W2[[v[i]+1]])
    wyniki[4,i]=wyniki[4,i]+Sub_dist(Vdok,W3[[v[i]+1]])
    
  }
  wyniki[,i]=wyniki[,i]/M
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.3),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")
grid(lwd=2)
}
######################################################
# identyczne macierze prawdopodobienstw niesymertycze
{B=matrix(data=c(0.4,0.4,0.1, 0.3,0.5,0.2, 0.1,0.1,0.6),nrow=3)
v=c(1,5,10,15,20,30,50,70,100)
M=50
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  P=gen.pn(B,Z,v[i])
  for (j in 1:M){
  A=mlos(P)
  W=MASE_unscaled(A,3)
  W1=MASE(A,3)
  W2=MLSE(A,0,3)
  W3=ASE.Mean(A,3)
  wyniki[1,i]=wyniki[1,i]+Sub_dist(Vdok,W[[v[i]+1]])
  wyniki[2,i]=wyniki[2,i]+Sub_dist(Vdok,W1[[v[i]+1]])
  wyniki[3,i]=wyniki[3,i]+Sub_dist(Vdok,W2[[v[i]+1]])
  wyniki[4,i]=wyniki[4,i]+Sub_dist(Vdok,W3[[v[i]+1]])
   
  }
  wyniki[,i]=wyniki[,i]/M
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.75),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="legenda")
grid(lwd=2)
}
######################################################
# losowe macierze prawdopodobienstw 
{
v=c(1,5,10,15,20,30,50,70,100)
M=100
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  R=gen.R(v[i],3)
  P=gen.p(R,Z)
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,0,3)
    W3=ASE.Mean(A,3)
    wyniki[1,i]=wyniki[1,i]+Sub_dist(Vdok,W[[v[i]+1]])
    wyniki[2,i]=wyniki[2,i]+Sub_dist(Vdok,W1[[v[i]+1]])
    wyniki[3,i]=wyniki[3,i]+Sub_dist(Vdok,W2[[v[i]+1]])
    wyniki[4,i]=wyniki[4,i]+Sub_dist(Vdok,W3[[v[i]+1]])
    
  }
  wyniki[,i]=wyniki[,i]/M
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.7),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")
grid(lwd=2)
}
######################################################
# losowe macierze prawdopodobienstw V R U^T 
{
v=c(1,5,10,15,20,30,50,70,100)
M=100
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  R=gen.R(v[i],3)
  P=gen.p2(R,Z,tas(Z))
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,0,3)
    W3=ASE.Mean(A,3)
    wyniki[1,i]=wyniki[1,i]+Sub_dist(Vdok,W[[v[i]+1]])
    wyniki[2,i]=wyniki[2,i]+Sub_dist(Vdok,W1[[v[i]+1]])
    wyniki[3,i]=wyniki[3,i]+Sub_dist(Vdok,W2[[v[i]+1]])
    wyniki[4,i]=wyniki[4,i]+Sub_dist(Vdok,W3[[v[i]+1]])
    
  }
  wyniki[,i]=wyniki[,i]/M
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 1),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")
grid(lwd=2)
}
######################################################
#############         P EST         ##################
######################################################
# identyczne macierze prawdopodobienstw symertycze
{
  B=matrix(data=c(0.4,0.1,0.1, 0.1,0.5,0.2, 0.1,0.2,0.6),nrow=3)
  v=c(1,5,10,15,20,30,50,70,100)
  M=2
  l=length(v)
  Z=gen.Z(300,3)
  Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
  wyniki=matrix(data=0,nrow=4,ncol=l)
  for (i in 1:l){
    P=gen.pn(B,Z,v[i])
    for (j in 1:M){
      A=mlos(P)
      W=MASE_unscaled(A,3)
      W1=MASE(A,3)
      W2=MLSE(A,0,3)
      W3=ASE.Mean(A,3)
      for (k in 1:v[i]){
        p=P_est(W)
        P1=P_est(W1)
        P2=P_est(W2)
        P3=P_est(W3)
        wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],p[[k]])
        wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P1[[k]])
        wyniki[3,i]=wyniki[3,i]+Frob_dist(P[[k]],P2[[k]])
        wyniki[4,i]=wyniki[4,i]+Frob_dist(P[[k]],P3[[k]])
      }
      
    }
    wyniki[,i]=wyniki[,i]/M/v[i]
  }
  
  plot(v,wyniki[1,],typ="o",ylim=c(0, 0.3),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
  grid(lwd=2)
  lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
  lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
  lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
  legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")

}
######################################################
# identyczne macierze prawdopodobienstw niesymertycze
{B=matrix(data=c(0.4,0.4,0.1, 0.3,0.5,0.2, 0.1,0.1,0.6),nrow=3)
v=c(1,5,10,15,20,30,50,70,100)
M=50
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  P=gen.pn(B,Z,v[i])
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,0,3)
    W3=ASE.Mean(A,3)
    for (k in 1:v[i]){
      p=P_est(W)
      P1=P_est(W1)
      P2=P_est(W2)
      P3=P_est(W3)
      wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],p[[k]])
      wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P1[[k]])
      wyniki[3,i]=wyniki[3,i]+Frob_dist(P[[k]],P2[[k]])
      wyniki[4,i]=wyniki[4,i]+Frob_dist(P[[k]],P3[[k]])
    }
  }
  wyniki[,i]=wyniki[,i]/M/v[i]
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.3),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
grid(lwd=2)
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")

}
######################################################
# losowe macierze prawdopodobienstw 
{v=c(1,5,10,15,20,30,50,70,100)
M=50
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  R=gen.R(v[i],3)
  P=gen.p(R,Z)
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,300,3)
    W3=ASE.Mean(A,3)
    for (k in 1:v[i]){
      p=P_est(W)
      P1=P_est(W1)
      P2=P_est(W2)
      P3=P_est(W3)
      wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],p[[k]])
      wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P1[[k]])
      wyniki[3,i]=wyniki[3,i]+Frob_dist(P[[k]],P2[[k]])
      wyniki[4,i]=wyniki[4,i]+Frob_dist(P[[k]],P3[[k]])
    }
    
  }
  wyniki[,i]=wyniki[,i]/M/v[i]
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.3),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
grid(lwd=2)
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")
}
######################################################
# losowe macierze prawdopodobienstw V R U^T 
{
v=c(1,5,10,15,20,30,50,70,100)
M=50
l=length(v)
Z=gen.Z(300,3)
Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
wyniki=matrix(data=0,nrow=4,ncol=l)
for (i in 1:l){
  R=gen.R(v[i],3)
  P=gen.p2(R,Z,tas(Z))
  for (j in 1:M){
    A=mlos(P)
    W=MASE_unscaled(A,3)
    W1=MASE(A,3)
    W2=MLSE(A,0,3)
    W3=ASE.Mean(A,3)
    for (k in 1:v[i]){
      p=P_est(W)
      P1=P_est(W1)
      P2=P_est(W2)
      P3=P_est(W3)
      wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],p[[k]])
      wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P1[[k]])
      wyniki[3,i]=wyniki[3,i]+Frob_dist(P[[k]],P2[[k]])
      wyniki[4,i]=wyniki[4,i]+Frob_dist(P[[k]],P3[[k]])
    }
    
  }
  wyniki[,i]=wyniki[,i]/M/v[i]
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.9),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
grid(lwd=2)
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
lines(v,wyniki[3,],col="red",typ="o",lwd=2,pch=3,cex=1.3)
lines(v,wyniki[4,],col="blue",typ="o",lwd=2,pch=4,cex=1.3)
legend('topright',inset=0.05,c("Unscaled MASE","Scaled MASE","MLSE","ASE(mean)"),pch=c(1,2,3,4),lty=1,col=c("black","green","red","blue"),title="Legenda")

}
######################################################
##########       1 Graf vs wiele         #############
######################################################
{
v=c(1,2,5,10,15,20,30)
M=100
l=length(v)
Z=gen.Z(300,3)
wyniki=matrix(data=0,nrow=2,ncol=l)
for (i in 1:l){
  R=gen.R(v[i],3)
  P=gen.p(R,Z)
  for (j in 1:M){
    A=mlos(P)
    W1=MASE(A,3)
    P1=P_est(W1)
    P2=ASE.list(A,3)
    for (k in 1:v[i]){
      wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],P1[[k]])
      wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P2[[k]])
    }
    
  }
  wyniki[,i]=wyniki[,i]/M/v[i]
}

plot(v,wyniki[1,],typ="o",ylim=c(0, 0.3),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
grid(lwd=2)
lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
legend('right',inset=0.05,c("MASE","ASE"),pch=c(1,2),lty=1,col=c("black","green"),title="legenda")
}
######################################################
#############         V vs V + U          ############
######################################################
{
Z=gen.Z(100,4)[,c(1,2)]
Z2=gen.Z(100,4)[,c(3,4)]
V_dok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
R=list(runi(2),runi(2),runi(2))
P2=gen.p2(R,Z,Z2)
P=gen.p(R,Z)
A=mlos(P)
B=mlos(P2)

W=MASE(A)
W1=MASE_UV(A)
Q=MASE(B)
Q1=MASE_UV(B)

{v=c(1:15)
  Z=gen.Z(300,3)
  Vdok=Z%*%(diag2(1/sqrt(diag(t(Z)%*%Z))))
  wyniki=matrix(data=0,nrow=4,ncol=15)
  for (i in v){
    R=gen.R(i,3)
    P=gen.p2(R,Z,tas(Z))
    for (j in 1:2){
      A=mlos(P)
      W1=MASE(A,3)
      W2=MASE_UV(A,3)
      for (k in 1:i){
        P1=P_est(W1)
        P2=P_est2(W2)
        wyniki[1,i]=wyniki[1,i]+Frob_dist(P[[k]],P1[[k]])
        wyniki[2,i]=wyniki[2,i]+Frob_dist(P[[k]],P2[[k]])
      }
      
    }
    wyniki[,i]=wyniki[,i]/2/i
  }
  
  plot(v,wyniki[1,],typ="o",ylim=c(0, 1),lwd=2,pch=1,cex=1.3,xlab="Liczba grafów",ylab="Œredni b³¹d estymacji")
  lines(v,wyniki[2,],col="green",typ="o",lwd=2,pch=2,cex=1.3)
  legend('topright',inset=0.05,c("Scaled MASE","MASE UV"),pch=c(1,2),lty=1,col=c("black","green"),title="legenda")
}


}
######################################################
############# Zwiekszanie liczby grafów  #############
######################################################
## Histogram dla wartosci osobliwych
{
Z=gen.Z(256,2)
B1 = diag(2)*0.3 + 0.1
P=gen.pn(B1,Z,20)
ldok=svd(P[[1]])$d
n=1000
{l=list()
m=2
for (i in 1:n){
  A=mlos(P[1:m])
  W=MASE(A)
  l[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
}}
{l2=list()
m=5
for (i in 1:n){
  A=mlos(P[1:m])
  W=MASE(A,2)
  l2[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
}}
{l3=list()
  m=20
  for (i in 1:n){
    A=mlos(P)
    W=MASE(A)
    l3[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
  }} 

{par(mfrow=c(2,3))
  
  lambda1=as.numeric(lapply(X=l,FUN=get,k=1))
  lambda2=as.numeric(lapply(X=l2,FUN=get,k=1))
  lambda3=as.numeric(lapply(X=l3,FUN=get,k=1))
  lambda11=as.numeric(lapply(X=l,FUN=get,k=2))
  lambda22=as.numeric(lapply(X=l2,FUN=get,k=2))
  lambda33=as.numeric(lapply(X=l3,FUN=get,k=2))
  q=60
  h<-hist(lambda1-ldok[1],freq=FALSE,ylab="Gêstoœæ",main="2 grafy",xlab="",breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda1)-ldok[1],col="red",lty=5,lwd=2)
  h2<-hist(lambda2-ldok[1],freq=FALSE,main="5 grafów",ylab="",xlab="",breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda2)-ldok[1],col="red",lty=5,lwd=2)
  h3<-hist(lambda3-ldok[1],freq=FALSE,main="20 grafów",ylab="",xlab="",breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda3)-ldok[1],col="red",lty=5,lwd=2)
  
  h11<-hist(lambda11-ldok[2],freq=FALSE,ylab="Gêstoœæ",main="",xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda11)-ldok[2],col="red",lty=5,lwd=2)
  h22<-hist(lambda22-ldok[2],freq=FALSE,ylab="",main="",xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda22)-ldok[2],col="red",lty=5,lwd=2)
  h33<-hist(lambda33-ldok[2],freq=FALSE,ylab="",main="",xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = q)
  grid()
  abline(v=0,col="darkblue",lwd=2,lty=1)
  abline(v=mean(lambda33)-ldok[2],col="red",lty=5,lwd=2)
}
}
## Blad estymacji wartosci osobliwych
{
  c = c(1,2,4, 5, 10, 15, 20, 30)
  N=100
  a=length(c)
  l1 = numeric(a)
  l2 = numeric(a)
  Z = gen.Z(600, 2)
  P = gen.pn(matrix(data=diag(2)*0.3 + 0.1,nrow=2), Z,c[a])
  d=svd(P[[1]])[[1]]
  lambda1=d[1]
  lambda2=d[2]
  for(j in 1:a){
    print(j)
    for (i in 1:N) {
      A = mlos(P[c(1:c[j])])
      S = MASE(A,2)
      for (k in 1:c[j]){
      F=svd(S[[k]])[[1]]
      l1[j]=l1[j]+abs(F[1]-lambda1)
      l2[j]=l2[j]+abs(F[2]-lambda2)
      }}
    l1[j]=l1[j]/N/c[j]
    l2[j]=l2[j]/N/c[j]
  } 
plot(c,l1,xlab="Liczba grafów",ylab="B³¹d estymacji",type="o",lwd=3,pch=1,cex=1.2,main="Pierwsza wartoœæ osobliwa")
grid(lwd=2)
plot(c,l2,xlab="Liczba grafów",ylab="B³¹d estymacji",type="o",lwd=3,pch=1,cex=1.2,main="Druga wartoœæ osobliwa")
grid(lwd=2)
}
######################################################
########## Zwiekszanie liczby wierzcholkow  ##########
######################################################
## Histogram dla wartosci osobliwych
{
  m=3
  n=100
  {t=list()
    Z=gen.Z(75,2)
    P = gen.pn(matrix(data=diag(2)*0.3 + 0.1,nrow=2), Z,m)
    ldok6=svd(P[[1]])$d
    for (i in 1:(n*10)){
      A=mlos(P)
      W=MASE(A,2)
      t[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
    }}
  {t2=list()
    Z=gen.Z(250,2)
    P = gen.pn(matrix(data=diag(2)*0.3 + 0.1,nrow=2), Z,m)
    ldok7=svd(P[[1]])$d
    for (i in 1:(n*4)){
      A=mlos(P)
      W=MASE(A,2)
      t2[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
    }}
  {t3=list()
    Z=gen.Z(500,2)
    P = gen.pn(matrix(data=diag(2)*0.3 + 0.1,nrow=2), Z,m)
    ldok8=svd(P[[1]])$d
    for (i in 1:n){
      A=mlos(P)
      W=MASE(A,2)
      t3[i]=list(svd(W[[m+1]]%*%W[[1]]%*%t(W[[m+1]]))$d)
    }} 
  
  {par(mfrow=c(2,3))
    
    lambda6=as.numeric(lapply(X=t,FUN=get,k=1))
    lambda7=as.numeric(lapply(X=t2,FUN=get,k=1))
    lambda8=as.numeric(lapply(X=t3,FUN=get,k=1))
    lambda66=as.numeric(lapply(X=t,FUN=get,k=2))
    lambda77=as.numeric(lapply(X=t2,FUN=get,k=2))
    lambda88=as.numeric(lapply(X=t3,FUN=get,k=2))
    h<-hist(lambda6-ldok6[1],freq=FALSE,main="75 wierzcho³ków",ylab="Gêstoœæ",xlim=c(-1.5+mean(lambda6)-ldok6[1],1.5+mean(lambda6)-ldok6[1]),xlab="",breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda6)-ldok6[1],col="red",lty=5,lwd=2)
    h2<-hist(lambda7-ldok7[1],freq=FALSE,main="250 wierzcho³ków",ylab="",xlim=c(-1.5+mean(lambda7)-ldok7[1],1.5+mean(lambda7)-ldok7[1]),xlab="",breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda7)-ldok7[1],col="red",lty=5,lwd=2)
    h3<-hist(lambda8-ldok8[1],freq=FALSE,main="500 wierzcho³ków",ylab="",xlim=c(-1.5,1.5),xlab="",breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda8)-ldok8[1],col="red",lty=5,lwd=2)
    
    h11<-hist(lambda66-ldok6[2],freq=FALSE,main="",ylab="Gêstoœæ",xlim=c(-1.5+mean(lambda66)-ldok6[2],1.5+mean(lambda66)-ldok6[2]),xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda66)-ldok6[2],col="red",lty=5,lwd=2)
    h22<-hist(lambda77-ldok7[2],freq=FALSE,main="",ylab="",xlim=c(-1.5+mean(lambda77)-ldok7[2],1.5+mean(lambda77)-ldok7[2]),xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda77)-ldok7[2],col="red",lty=5,lwd=2)
    h33<-hist(lambda88-ldok8[2],freq=FALSE,main="",ylab="",xlim=c(-1.5,1.5),xlab=expression(paste(  tilde(lambda) -  lambda)),breaks = 40)
    grid()
    abline(v=0,col="darkblue",lwd=2,lty=1)
    abline(v=mean(lambda88)-ldok8[2],col="red",lty=5,lwd=2)
  }
}
## Blad estymacji wartosci osobliwych
{
  c = c(100,200,400,600,900,1500)
  N=70
  a=length(c)
  l1 = numeric(a)
  l2 = numeric(a)
 
  for(j in 1:a){
    print(j)
    Z = gen.Z(c[j], 2)
    P = gen.pn(matrix(data=diag(2)*0.3 + 0.1,nrow=2), Z,4)
    d=svd(P[[1]])[[1]]
    lambda1=d[1]
    lambda2=d[2]
    for (i in 1:N) {
      A = mlos(P)
      S = MASE(A,2)
      F=svd(S[[5]]%*%S[[1]]%*%t(S[[5]]))[[1]]
      l1[j]=l1[j]+abs(F[1]-lambda1)
      l2[j]=l2[j]+abs(F[2]-lambda2)
    }
    l1[j]=l1[j]/N
    l2[j]=l2[j]/N
  } 
  plot(c,l1,xlab="Liczba wierzcho³ków",ylab="B³¹d estymacji",type="o",lwd=3,pch=1,cex=1.2,main="Pierwsza wartoœæ osobliwa")
  grid(lwd=2)
  plot(c,l2,xlab="Liczba wierzcho³ków",ylab="B³¹d estymacji",type="o",lwd=3,pch=1,cex=1.2,main="Druga wartoœæ osobliwa")
  grid(lwd=2)
}
######################################################
#####################    Heatmap    ##################
######################################################
{
Z=gen.Z(400,8)
R=gen.R(10,8)
P=gen.p(R,Z)
A=mlos(P)
levelplot(t(A[[1]][400:1,]),col.regions=heat.colors(4))

library(viridisLite)
levelplot(t(A[[1]][400:1,]),col.regions=magma(100))
R[[1]]}
######################################################
###############    Czas dzialania    #################
######################################################
{
Z=gen.Z(300,30)
R1=gen.R(2,30)
P1=gen.p(R1,Z)
A1=mlos(P1)
R2=gen.R(4,30)
P2=gen.p(R2,Z)
A2=mlos(P2)
R3=gen.R(6,30)
P3=gen.p(R3,Z)
A3=mlos(P3)
R4=gen.R(8,30)
P4=gen.p(R4,Z)
A4=mlos(P4)
R5=gen.R(10,30)
P5=gen.p(R5,Z)
A5=mlos(P5)
R6=gen.R(15,30)
P6=gen.p(R6,Z)
A6=mlos(P6)
R7=gen.R(20,30)
P7=gen.p(R7,Z)
A7=mlos(P7)
R8=gen.R(25,30)
P8=gen.p(R8,Z)
A8=mlos(P8)
R9=gen.R(30,30)
P9=gen.p(R9,Z)
A9=mlos(P9)
R10=gen.R(35,30)
P10=gen.p(R10,Z)
A10=mlos(P10)
t=microbenchmark::microbenchmark(
  "2"=MASE(A1),
  "4"=MASE(A2),
  "6"=MASE(A3),
  "8"=MASE(A4),
  "10"=MASE(A5),
  "15"=MASE(A6),
  "20"=MASE(A7),
  "25"=MASE(A8),
  "30"=MASE(A9),
  "35"=MASE(A10),
  times = 2,
  unit="s"
)
t2=microbenchmark::microbenchmark(
  "2"=MASE_UV(A1),
  "4"=MASE_UV(A2),
  "6"=MASE_UV(A3),
  "8"=MASE_UV(A4),
  "10"=MASE_UV(A5),
  "15"=MASE_UV(A6),
  "20"=MASE_UV(A7),
  "25"=MASE_UV(A8),
  "30"=MASE_UV(A9),
  "35"=MASE_UV(A10),
  times = 2,
  unit="s"
)
t$expr=as.numeric(levels(t$expr)[t$expr])
time=t %>% group_by(expr) %>% summarise(Czas=mean(time/10^9))
t2$expr=as.numeric(levels(t2$expr)[t2$expr])
time2=t2 %>% group_by(expr) %>% summarise(Czas=mean(time/10^9))
plot(time,xla="Liczba grafów",type="o",lty=1,lwd=4)
m=as.matrix(time2)
lines(x=m[,1],y=m[,2],type="o",lty=1,lwd=4,col="darkgray")
}
{
  d=4
  R=gen.R(4,d)
  Z1=gen.Z(40,4)
  P1=gen.p(R,Z1)
  A1=mlos(P1)
  Z2=gen.Z(100,4)
  P2=gen.p(R,Z2)
  A2=mlos(P2)
  Z3=gen.Z(200,4)
  P3=gen.p(R,Z3)
  A3=mlos(P3)
  Z4=gen.Z(400,4)
  P4=gen.p(R,Z4)
  A4=mlos(P4)
  Z5=gen.Z(600,4)
  P5=gen.p(R,Z5)
  A5=mlos(P5)
  Z6=gen.Z(800,4)
  P6=gen.p(R,Z6)
  A6=mlos(P6)
  Z7=gen.Z(1000,4)
  P7=gen.p(R,Z7)
  A7=mlos(P7)
  Z8=gen.Z(1200,4)
  P8=gen.p(R,Z8)
  A8=mlos(P8)
  Z9=gen.Z(1600,4)
  P9=gen.p(R,Z9)
  A9=mlos(P9)
  Z10=gen.Z(2000,4)
  P10=gen.p(R,Z10)
  A10=mlos(P10)
  t=microbenchmark::microbenchmark(
    "40"=MASE(A1),
    "100"=MASE(A2),
    "200"=MASE(A3),
    "400"=MASE(A4),
    "600"=MASE(A5),
    "800"=MASE(A6),
    "1000"=MASE(A7),
    "1200"=MASE(A8),
    "1600"=MASE(A9),
    "2000"=MASE(A10),
    times = 1,
    unit="s"
  )
  t$expr=as.numeric(levels(t$expr)[t$expr])
  time=t %>% group_by(expr) %>% summarise(Czas=mean(time/10^9))
  plot(time,xla="Liczba wierzcho³ków",type="o",lty=1,lwd=4)
}
######################################################
############    Klasyfikacja grafow    ###############
######################################################
{
C=matrix(data=c(0.4,0.4,0.4,0.4),nrow=2)
alfa=c(0,0.1,0.3,0.5,0.75,1,1.5,2)
N=100

a=length(alfa)
Z=gen.Z(256,2)
id1=matrix(data=c(0.1,0,0,0.1),nrow=2)
id2=matrix(data=c(0,0,0,0.1),nrow=2)
id3=matrix(data=c(0.1,0,0,0),nrow=2)
id4=matrix(data=c(0.1,0,0,-0.1),nrow=2)
acc=matrix(numeric(a*N),nrow=N)
acc2=matrix(numeric(a*N),nrow=N)
for (i in 1:a){
M=list()
M[1]=list(C+alfa[i]*id1)
M[2]=list(C+alfa[i]*id2)
M[3]=list(C+alfa[i]*id3)
M[4]=list(C+alfa[i]*id4)
G=rep(M,10)
L=rep(c(1,2,3,4),10)
P=gen.p(G,Z)  
for (j in 1:N){
A=mlos(P)
W=MASE(A,2)

LTrain=L[1:20]
LTest=L[21:40]

Train=W[1:20]
Test=W[21:40]
Train2=A[1:20]
Test2=A[21:40]

Est=Frob_class(Test,Train,LTest)
Est2=Frob_class(Test2,Train2,LTest)
acc[j,i]=sum(Est==LTest)/20
acc2[j,i]=sum(Est2==LTest)/20}}
w=apply(acc,FUN="mean",MARGIN = 2)
w2=apply(acc2,FUN="mean",MARGIN = 2)
plot(alfa,w,xlab="Separacja klas",ylab="Dok³adnoœæ",type="o",lwd=2,pch=1,cex=1.3)
lines(alfa,w2,type="o",lwd=2,pch=3,cex=1.3,col="green")
grid(lwd=2)
legend('bottomright',inset=0.05,c("MASE","Naive"),pch=c(1,3),lty=1,col=c("black","green"),title="legenda")
}
######################################################
#########    Klasyfikacja wierzcho³ków    ############
######################################################
{
  C=matrix(data=c(0.4,0.4,0.4,0.4),nrow=2)
  alfa=c(0.01,0.1,0.3,0.4,0.45,0.5,0.6,0.75,0.9,1,1.5)
  N=40
  a=length(alfa)
  Z=gen.Z(400,2)
  id1=matrix(data=c(0.1,0,0,0.1),nrow=2)
  id2=matrix(data=c(0,0,0,0.1),nrow=2)
  id3=matrix(data=c(0.1,0,0,0),nrow=2)
  id4=matrix(data=c(0.1,0,0,-0.1),nrow=2)
  acc=matrix(numeric(a*N),nrow=N)
  acc2=matrix(numeric(a*N),nrow=N)
  acc3=matrix(numeric(a*N),nrow=N)
  for (i in 1:a){
    print(i)
    M=list()
    M[1]=list(C+alfa[i]*id1)
    M[2]=list(C+alfa[i]*id2)
    M[3]=list(C+alfa[i]*id3)
    M[4]=list(C+alfa[i]*id4) 
    G=rep(M,10)
    L=rep(c(1,2,3,4),10)
    P=gen.p(G,Z)  
    for (j in 1:N){
      A=mlos(P)
      W=MASE(A,2)
      W2=MASE(A[1:20],2)
      W3=MASE(A[1:8],2)
      gmm = GMM(W[[41]], 2, dist_mode = "maha_dist", seed_mode = "random_subset", km_iter = 10,
                em_iter = 10, verbose = F) 
      pr = predict(gmm, newdata = W[[41]])
      gmm2 = GMM(W2[[21]], 2, dist_mode = "maha_dist", seed_mode = "random_subset", km_iter = 10,
                em_iter = 10, verbose = F) 
      pr2 = predict(gmm2, newdata = W2[[21]])
      gmm3 = GMM(W3[[9]], 2, dist_mode = "maha_dist", seed_mode = "random_subset", km_iter = 10,
                 em_iter = 10, verbose = F) 
      pr3 = predict(gmm3, newdata = W3[[9]])
      acc[j,i]=(max(sum(pr[1:200]==1),sum(pr[201:400]==1))+max(sum(pr[1:200]==2),sum(pr[201:400]==2)))/400
      acc2[j,i]=(max(sum(pr2[1:200]==1),sum(pr2[201:400]==1))+max(sum(pr2[1:200]==2),sum(pr2[201:400]==2)))/400
      acc3[j,i]=(max(sum(pr3[1:200]==1),sum(pr3[201:400]==1))+max(sum(pr3[1:200]==2),sum(pr3[201:400]==2)))/400
            }}
  w=apply(acc,FUN="mean",MARGIN = 2)
  w2=apply(acc2,FUN="mean",MARGIN = 2)
  w3=apply(acc3,FUN="mean",MARGIN = 2)
  plot(alfa,w,xlab="Separacja klas",ylab="Dok³adnoœæ",ylim=c(0.5,1),type="o",lwd=2,pch=1,cex=1.3)
  lines(alfa,w2,type="o",lwd=2,pch=3,cex=1.3,col="green")
  lines(alfa,w3,type="o",lwd=2,pch=4,cex=1.3,col="blue")
  grid(lwd=2)
  legend('bottomright',inset=0.05,c("8 grafów","20 grafów","40 grafów"),pch=c(4,3,1),lty=1,col=c("blue","green","black"),title="Legenda")
}
######################################################
############    Testowanie hipotez   #################
######################################################
{Z=gen.Z(300,3)
  eps=c(0,0.01,0.015,0.02,0.025,0.03,0.04)
  B1 = diag(3)*0.3 + 0.1
  B2=B1
  N=200
  M=20
  power=matrix(0,M,length(eps))
  power1=matrix(0,M,length(eps))
  for (i in 1:length(eps)){
    print(i)
    B2[1,1]=B1[1,1]+eps[i]
    P=gen.p(list(B1,B2),Z)
    Dok=MASE(P,3)
    V=Dok[[3]]
    R1=Dok[[1]]
    R2=Dok[[2]]
    T=test_COSIE(V,R1,R2,N)
    for (j in 1:M){
    A=mlos(P)
    W=MASE(A,3)
    power[j,i]=max(pval(Frob(W[[1]],W[[2]]),T[[2]]),pval(Frob(W[[1]],W[[2]]),T[[3]]))<=0.05
    power1[j,i]=test_COSIE(W[[3]],W[[1]],W[[2]],N)[[1]]<=0.05}
  }
  pow1=apply(power,FUN="mean",MARGIN = 2)
  pow2=apply(power1,FUN="mean",MARGIN = 2)
  plot(eps,pow1,type="o",xlab="Separacja klas",ylab="Moc testu",lwd=2.5,pch=1,cex=1.3)
  lines(eps,pow2,type="o",col="green",lwd=2.5,pch=3,cex=1.3)
  grid(lwd=2)
  abline(a=0.05,b=0,lwd=2,lty=2,col="darkgrey")
}
{
  Z=gen.Z(300,3)
  eps=c(0,0.01,0.015,0.02,0.025,0.03,0.04)
  N=20000
  M=100
  B1 = diag(3)*0.3 + 0.1
  B2=B1
  z=rep(0,9)
  power2=matrix(0,M,length(eps))
  for (i in 1:length(eps)){
    B2[1,1]=B1[1,1]+eps[i]
    P=gen.p(list(B1,B2),Z)
    for (j in 1:M){
      A=mlos(P)
      W=MASE(A,3)
      EP1=pm(W[[3]]%*%W[[1]]%*%t(W[[3]]))
      EP2=pm(W[[3]]%*%W[[2]]%*%t(W[[3]]))
      sig1=sig(EP1,W[[3]])
      sig2=sig(EP2,W[[3]])
      L=rmvnorm(N,z,2*sig1)
      L2=rmvnorm(N,z,2*sig2)
      F=apply(L,FUN=function(x){ return(norm(matrix(x),"F"))},MARGIN=1)
      F2=apply(L2,FUN=function(x){ return(norm(matrix(x),"F"))},MARGIN=1)
      power2[j,i]=max(pval(Frob(W[[1]],W[[2]]),F),pval(Frob(W[[1]],W[[2]]),F2))<0.05
      }
  }
  r=apply(power2,FUN="mean",MARGIN = 2)
  lines(eps,r,type="o",col="blue",lwd=2.5,pch=4,cex=1.3)
  legend('topleft',inset=0.05,c("MASE","MASE Bootstrap","MASE Asymptotic"),lwd=2,pch=c(1,2,4),lty=1,col=c("black","green","blue"),title="Legenda")
  
  }




