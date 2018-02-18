"""

January 26, 2016

Instructions:

Load this file and the file of your choice. For example:

sage: load("./sage-instructions.sage")
sage: load("./qexps_601-800.sage")

This creates a list "eigenforms_list" whose entries are triples [fourier_coeffs,P_coeffs,eps_data] with

fourier_coeffs:     the Fourier coefficients of a cuspidal eigenform f which is new in level N with character eps,
                    to precision the Sturm bound for S_2(N). (Each Fourier coefficients is given as a list of
                    rational numbers, representing an element in the number field defined by the polynomial P below.)

P_coeffs:           the coefficients of the polynomial P defining the number field over which the Fouriers coefficients are defined

eps_data:           a list of length two whose first entry is the modulus N of the odd character "eps"
                    and whose second entry defines the character uniquely in terms of the image of generators
                    for (Z/NZ)^* under the character.

The encoding of the form f itself is intended to be easily sage readable, rather than human readable. The
function make_form() should be applied to a each triple to recover the q-expansion of f, as a power series, and character.

Continuing the above example:

sage: fs = eigenforms_list[42]
sage: f,eps = make_form(fs)
sage: f
q + b*q^2 + q^3 - b*q^4 + q^5 + b*q^6 + b*q^7 - q^8 + q^9 + b*q^10 + (-b - 1)*q^11 - b*q^12 + (-b - 1)*q^13 + (-b + 1)*q^14 + q^15 + b*q^18 - b*q^20 + b*q^21 - q^22 + (-b - 1)*q^23 - q^24 + q^25 - q^26 + q^27 + (b - 1)*q^28 + b*q^29 + b*q^30 + b*q^31 + q^32 + (-b - 1)*q^33 + b*q^35 - b*q^36 + (-b - 1)*q^39 - q^40 + q^41 + (-b + 1)*q^42 + q^44 + q^45 - q^46 - b*q^49 + b*q^50 + q^52 + b*q^54 + (-b - 1)*q^55 - b*q^56 + (-b + 1)*q^58 - b*q^60 + (-b - 1)*q^61 + (-b + 1)*q^62 + b*q^63 + b*q^64 + (-b - 1)*q^65 - q^66 + (-b - 1)*q^67 + (-b - 1)*q^69 + (-b + 1)*q^70 + b*q^71 - q^72 + q^75 - q^77 - q^78 + q^81 + b*q^82 + b*q^83 + (b - 1)*q^84 + b*q^87 + (b + 1)*q^88 + b*q^89 + b*q^90 - q^91 + q^92 + b*q^93 + q^96 + b*q^97 + (b - 1)*q^98 + (-b - 1)*q^99 - b*q^100 + 2*q^101 + (b + 1)*q^104 + b*q^105 + (-b - 1)*q^107 - b*q^108 - q^110 + b*q^113 + (-b - 1)*q^115 + (b - 1)*q^116 + (-b - 1)*q^117 - q^120 + (b + 1)*q^121 - q^122 + q^123 + (b - 1)*q^124 + q^125 + (-b + 1)*q^126 - b*q^128 - q^130 + q^132 - q^134 + q^135 - q^138 + b*q^139 + (b - 1)*q^140 + (-b + 1)*q^142 + (b + 2)*q^143 + b*q^145 - b*q^147 + (-b - 1)*q^149 + b*q^150 - b*q^154 + b*q^155 + q^156 + b*q^157 + q^160 + O(q^161)
sage: eps
Dirichlet character modulo 615 of conductor 615 mapping 206 |--> -1, 247 |--> -1, 211 |--> -1
sage: f.parent()
Power Series Ring in q over Number Field in b with defining polynomial a^2 + a - 1

To obtain more q-expansion coefficients in f use the function extend_qexpansion():

sage: F = extend_qexpansion(f,eps,200)
sage: F
q + b*q^2 + q^3 - b*q^4 + q^5 + b*q^6 + b*q^7 - q^8 + q^9 + b*q^10 + (-b - 1)*q^11 - b*q^12 + (-b - 1)*q^13 + (-b + 1)*q^14 + q^15 + b*q^18 - b*q^20 + b*q^21 - q^22 + (-b - 1)*q^23 - q^24 + q^25 - q^26 + q^27 + (b - 1)*q^28 + b*q^29 + b*q^30 + b*q^31 + q^32 + (-b - 1)*q^33 + b*q^35 - b*q^36 + (-b - 1)*q^39 - q^40 + q^41 + (-b + 1)*q^42 + q^44 + q^45 - q^46 - b*q^49 + b*q^50 + q^52 + b*q^54 + (-b - 1)*q^55 - b*q^56 + (-b + 1)*q^58 - b*q^60 + (-b - 1)*q^61 + (-b + 1)*q^62 + b*q^63 + b*q^64 + (-b - 1)*q^65 - q^66 + (-b - 1)*q^67 + (-b - 1)*q^69 + (-b + 1)*q^70 + b*q^71 - q^72 + q^75 - q^77 - q^78 + q^81 + b*q^82 + b*q^83 + (b - 1)*q^84 + b*q^87 + (b + 1)*q^88 + b*q^89 + b*q^90 - q^91 + q^92 + b*q^93 + q^96 + b*q^97 + (b - 1)*q^98 + (-b - 1)*q^99 - b*q^100 + 2*q^101 + (b + 1)*q^104 + b*q^105 + (-b - 1)*q^107 - b*q^108 - q^110 + b*q^113 + (-b - 1)*q^115 + (b - 1)*q^116 + (-b - 1)*q^117 - q^120 + (b + 1)*q^121 - q^122 + q^123 + (b - 1)*q^124 + q^125 + (-b + 1)*q^126 - b*q^128 - q^130 + q^132 - q^134 + q^135 - q^138 + b*q^139 + (b - 1)*q^140 + (-b + 1)*q^142 + (b + 2)*q^143 + b*q^145 - b*q^147 + (-b - 1)*q^149 + b*q^150 - b*q^154 + b*q^155 + q^156 + b*q^157 + q^160 - q^161 + b*q^162 - b*q^164 + (-b - 1)*q^165 + (-b + 1)*q^166 - b*q^168 + (b + 1)*q^169 + (-b - 1)*q^173 + (-b + 1)*q^174 + b*q^175 + (-b + 1)*q^178 + 2*q^179 - b*q^180 - b*q^182 + (-b - 1)*q^183 + (b + 1)*q^184 + (-b + 1)*q^186 + b*q^189 + b*q^191 + b*q^192 + (-b - 1)*q^193 + (-b + 1)*q^194 + (-b - 1)*q^195 + (-b + 1)*q^196 + b*q^197 - q^198 + O(q^200)


"""

def make_qexpansion(fs):


    Qa.<a> = PolynomialRing(Rationals())
    fourier_coeffs = fs[0]
    P_coeffs = fs[1]
    P = sum([P_coeffs[i]*a^i for i in range(0,len(P_coeffs))]) # defining polynomial
    C.<b> = NumberField(P)
    Cq.<q> = PowerSeriesRing(C,len(fourier_coeffs) + 2)
    deg = P.degree()
    
    f = Cq(0)

    
    for n in range (0,len(fourier_coeffs)):
        fn = C(0)
        for i in range(0,deg):
            fn = fn + fourier_coeffs[n][i]*b^i
        f = f + fn*q^(n+1)
    
    return f + O(q^(len(fourier_coeffs) + 1))


def make_character(eps_data,P_coeffs):

    Qa.<a> = PolynomialRing(Rationals())
    P = sum([P_coeffs[i]*a^i for i in range(0,len(P_coeffs))]) # defining polynomial
    C.<b> = NumberField(P)
    N = eps_data[0]
    G = DirichletGroup(N,C)
    deg = P.degree()
    
    eps_gens = eps_data[1]
    eps_gens_C = [] # need to map images of generators from polynomial ring Qa to C
    
    for i in range(0,len(eps_gens)):
        x = eps_gens[i][0]
        y = eps_gens[i][1]    
        if y.parent() == Integers():
            eps_gens_C.append([x,y])
        else:
            y_C = C(0)
            for i in range(0,deg):
                y_C = y_C + y[i]*b^i
            eps_gens_C.append([x,y_C])
    
    for eps in G:
        if [eps(eps_gens_C[i][0]) == eps_gens_C[i][1] for i in range(0,len(eps_gens))] == [true for i in range(0,len(eps_gens))]:
            return eps
    
    assert true == false # error in make_character: cannot recognise Dirichlet character
    
    return 0 
    
def make_form(fs):

    f = make_qexpansion(fs)
    
    eps_data = fs[2]
    P_coeffs = fs[1]
    eps = make_character(eps_data,P_coeffs)
    
    return f, eps
    
def eisenstein_series_weight_one(eps,K,qprec): # returns E_1(1,eps) modulo q^qprec

    Sq.<q> = PowerSeriesRing(K,qprec)
    
    M = eps.conductor()
    eps_prim = eps.primitive_character()
    
    E_0 = (-1/M)*sum([j*eps_prim(j) for j in range(0,M)])
    
    E = (E_0/2) + sum([sum([eps_prim(n) for n in Integer(m).divisors()])*q^m for m in range(1,qprec)])
    
    return E
    
def write_in_basis(g,B): # writes a form g in terms of a basis B for the space in which it lies

    K = B[0][0].parent()
    g_vec = [K(0) for j in range(1,len(B) + 1)]
    for j in range(0,len(B)):
    	Bj_leadingpos = B[j].valuation()
        Bj_leadingcoeff = B[j][Bj_leadingpos]
        g_vec[j] = g[Bj_leadingpos]/Bj_leadingcoeff
        g = g - g_vec[j]*B[j]
        
#    assert g == 0
    
    return g_vec
    
def extend_qexpansion(f,eps,qprec): # returns the q-expansion of the weight one form f to precision q^qprec

    K = f[0].parent()
    
    E_epsinv = eisenstein_series_weight_one(eps^-1,K,qprec) # compute the weight one eisenstein series E_1(1,eps^-1)
    
    g = f*E_epsinv 
    # multiplying by the weight one eisenstein series gives a weight 2 form g, known to the smaller precision
    
    N = eps.modulus()
    B = CuspForms(N,2).basis() # find a basis for the space in which g lies
    B_K_qprec = [b.q_expansion(qprec) for b in B] # find the basis elements to higher precision
    
    Kq = f.parent()
    B_K = [Kq(b) for b in B_K_qprec] 
    g_vec = write_in_basis(g,B_K) # find the coefficients expressing g in this basis
    
    g_qprec = sum([g_vec[i]*B_K_qprec[i] for i in range(0,len(B))]) # now recover g to higher precision
    
    f_qprec = g_qprec*E_epsinv^-1 # dividing by the weight one Eisenstein series gives f to higher precision
    
    return f_qprec
    
