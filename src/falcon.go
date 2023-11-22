package falcon

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"

	"github.com/realForbis/go-falcon-WIP/src/internal"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/ntt"
	"github.com/realForbis/go-falcon-WIP/src/util"

	"golang.org/x/crypto/sha3"
)

//type (
//	Tree []any // LDL tree
//)

var RC = []uint64{
	0x0000000000000001, 0x0000000000008082,
	0x800000000000808A, 0x8000000080008000,
	0x000000000000808B, 0x0000000080000001,
	0x8000000080008081, 0x8000000000008009,
	0x000000000000008A, 0x0000000000000088,
	0x0000000080008009, 0x000000008000000A,
	0x000000008000808B, 0x800000000000008B,
	0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080,
	0x000000000000800A, 0x800000008000000A,
	0x8000000080008081, 0x8000000000008080,
	0x0000000080000001, 0x8000000080008008,
}

func process_block(A *[25]uint64) {
	var t0, t1, t2, t3, t4 uint64
	var tt0, tt1, tt2, tt3 uint64
	var t, kt uint64
	var c0, c1, c2, c3, c4, bnn uint64
	var j int

	/*
	 * Invert some words (alternate internal representation, which
	 * saves some operations).
	 */
	// ~x = -x-1
	A[1] = 0 - A[1] - 1
	A[2] = 0 - A[2] - 1
	A[8] = 0 - A[8] - 1
	A[12] = 0 - A[12] - 1
	A[17] = 0 - A[17] - 1
	A[20] = 0 - A[20] - 1

	/*
	 * Compute the 24 rounds. This loop is partially unrolled (each
	 * iteration computes two rounds).
	 */
	for j = 0; j < 24; j += 2 {

		tt0 = A[1] ^ A[6]
		tt1 = A[11] ^ A[16]
		tt0 ^= A[21] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[4] ^ A[9]
		tt3 = A[14] ^ A[19]
		tt0 ^= A[24]
		tt2 ^= tt3
		t0 = tt0 ^ tt2

		tt0 = A[2] ^ A[7]
		tt1 = A[12] ^ A[17]
		tt0 ^= A[22] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[0] ^ A[5]
		tt3 = A[10] ^ A[15]
		tt0 ^= A[20]
		tt2 ^= tt3
		t1 = tt0 ^ tt2

		tt0 = A[3] ^ A[8]
		tt1 = A[13] ^ A[18]
		tt0 ^= A[23] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[1] ^ A[6]
		tt3 = A[11] ^ A[16]
		tt0 ^= A[21]
		tt2 ^= tt3
		t2 = tt0 ^ tt2

		tt0 = A[4] ^ A[9]
		tt1 = A[14] ^ A[19]
		tt0 ^= A[24] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[2] ^ A[7]
		tt3 = A[12] ^ A[17]
		tt0 ^= A[22]
		tt2 ^= tt3
		t3 = tt0 ^ tt2

		tt0 = A[0] ^ A[5]
		tt1 = A[10] ^ A[15]
		tt0 ^= A[20] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[3] ^ A[8]
		tt3 = A[13] ^ A[18]
		tt0 ^= A[23]
		tt2 ^= tt3
		t4 = tt0 ^ tt2

		A[0] = A[0] ^ t0
		A[5] = A[5] ^ t0
		A[10] = A[10] ^ t0
		A[15] = A[15] ^ t0
		A[20] = A[20] ^ t0
		A[1] = A[1] ^ t1
		A[6] = A[6] ^ t1
		A[11] = A[11] ^ t1
		A[16] = A[16] ^ t1
		A[21] = A[21] ^ t1
		A[2] = A[2] ^ t2
		A[7] = A[7] ^ t2
		A[12] = A[12] ^ t2
		A[17] = A[17] ^ t2
		A[22] = A[22] ^ t2
		A[3] = A[3] ^ t3
		A[8] = A[8] ^ t3
		A[13] = A[13] ^ t3
		A[18] = A[18] ^ t3
		A[23] = A[23] ^ t3
		A[4] = A[4] ^ t4
		A[9] = A[9] ^ t4
		A[14] = A[14] ^ t4
		A[19] = A[19] ^ t4
		A[24] = A[24] ^ t4
		A[5] = (A[5] << 36) | (A[5] >> (64 - 36))
		A[10] = (A[10] << 3) | (A[10] >> (64 - 3))
		A[15] = (A[15] << 41) | (A[15] >> (64 - 41))
		A[20] = (A[20] << 18) | (A[20] >> (64 - 18))
		A[1] = (A[1] << 1) | (A[1] >> (64 - 1))
		A[6] = (A[6] << 44) | (A[6] >> (64 - 44))
		A[11] = (A[11] << 10) | (A[11] >> (64 - 10))
		A[16] = (A[16] << 45) | (A[16] >> (64 - 45))
		A[21] = (A[21] << 2) | (A[21] >> (64 - 2))
		A[2] = (A[2] << 62) | (A[2] >> (64 - 62))
		A[7] = (A[7] << 6) | (A[7] >> (64 - 6))
		A[12] = (A[12] << 43) | (A[12] >> (64 - 43))
		A[17] = (A[17] << 15) | (A[17] >> (64 - 15))
		A[22] = (A[22] << 61) | (A[22] >> (64 - 61))
		A[3] = (A[3] << 28) | (A[3] >> (64 - 28))
		A[8] = (A[8] << 55) | (A[8] >> (64 - 55))
		A[13] = (A[13] << 25) | (A[13] >> (64 - 25))
		A[18] = (A[18] << 21) | (A[18] >> (64 - 21))
		A[23] = (A[23] << 56) | (A[23] >> (64 - 56))
		A[4] = (A[4] << 27) | (A[4] >> (64 - 27))
		A[9] = (A[9] << 20) | (A[9] >> (64 - 20))
		A[14] = (A[14] << 39) | (A[14] >> (64 - 39))
		A[19] = (A[19] << 8) | (A[19] >> (64 - 8))
		A[24] = (A[24] << 14) | (A[24] >> (64 - 14))

		bnn = 0 - A[12] - 1 //~
		kt = A[6] | A[12]
		c0 = A[0] ^ kt
		kt = bnn | A[18]
		c1 = A[6] ^ kt
		kt = A[18] & A[24]
		c2 = A[12] ^ kt
		kt = A[24] | A[0]
		c3 = A[18] ^ kt
		kt = A[0] & A[6]
		c4 = A[24] ^ kt
		A[0] = c0
		A[6] = c1
		A[12] = c2
		A[18] = c3
		A[24] = c4
		bnn = 0 - A[22] - 1 //~
		kt = A[9] | A[10]
		c0 = A[3] ^ kt
		kt = A[10] & A[16]
		c1 = A[9] ^ kt
		kt = A[16] | bnn
		c2 = A[10] ^ kt
		kt = A[22] | A[3]
		c3 = A[16] ^ kt
		kt = A[3] & A[9]
		c4 = A[22] ^ kt
		A[3] = c0
		A[9] = c1
		A[10] = c2
		A[16] = c3
		A[22] = c4
		bnn = 0 - A[19] - 1 //~
		kt = A[7] | A[13]
		c0 = A[1] ^ kt
		kt = A[13] & A[19]
		c1 = A[7] ^ kt
		kt = bnn & A[20]
		c2 = A[13] ^ kt
		kt = A[20] | A[1]
		c3 = bnn ^ kt
		kt = A[1] & A[7]
		c4 = A[20] ^ kt
		A[1] = c0
		A[7] = c1
		A[13] = c2
		A[19] = c3
		A[20] = c4
		bnn = 0 - A[17] - 1 //~
		kt = A[5] & A[11]
		c0 = A[4] ^ kt
		kt = A[11] | A[17]
		c1 = A[5] ^ kt
		kt = bnn | A[23]
		c2 = A[11] ^ kt
		kt = A[23] & A[4]
		c3 = bnn ^ kt
		kt = A[4] | A[5]
		c4 = A[23] ^ kt
		A[4] = c0
		A[5] = c1
		A[11] = c2
		A[17] = c3
		A[23] = c4
		bnn = 0 - A[8] - 1 //~
		kt = bnn & A[14]
		c0 = A[2] ^ kt
		kt = A[14] | A[15]
		c1 = bnn ^ kt
		kt = A[15] & A[21]
		c2 = A[14] ^ kt
		kt = A[21] | A[2]
		c3 = A[15] ^ kt
		kt = A[2] & A[8]
		c4 = A[21] ^ kt
		A[2] = c0
		A[8] = c1
		A[14] = c2
		A[15] = c3
		A[21] = c4
		A[0] = A[0] ^ RC[j+0]

		tt0 = A[6] ^ A[9]
		tt1 = A[7] ^ A[5]
		tt0 ^= A[8] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[24] ^ A[22]
		tt3 = A[20] ^ A[23]
		tt0 ^= A[21]
		tt2 ^= tt3
		t0 = tt0 ^ tt2

		tt0 = A[12] ^ A[10]
		tt1 = A[13] ^ A[11]
		tt0 ^= A[14] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[0] ^ A[3]
		tt3 = A[1] ^ A[4]
		tt0 ^= A[2]
		tt2 ^= tt3
		t1 = tt0 ^ tt2

		tt0 = A[18] ^ A[16]
		tt1 = A[19] ^ A[17]
		tt0 ^= A[15] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[6] ^ A[9]
		tt3 = A[7] ^ A[5]
		tt0 ^= A[8]
		tt2 ^= tt3
		t2 = tt0 ^ tt2

		tt0 = A[24] ^ A[22]
		tt1 = A[20] ^ A[23]
		tt0 ^= A[21] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[12] ^ A[10]
		tt3 = A[13] ^ A[11]
		tt0 ^= A[14]
		tt2 ^= tt3
		t3 = tt0 ^ tt2

		tt0 = A[0] ^ A[3]
		tt1 = A[1] ^ A[4]
		tt0 ^= A[2] ^ tt1
		tt0 = (tt0 << 1) | (tt0 >> 63)
		tt2 = A[18] ^ A[16]
		tt3 = A[19] ^ A[17]
		tt0 ^= A[15]
		tt2 ^= tt3
		t4 = tt0 ^ tt2

		A[0] = A[0] ^ t0
		A[3] = A[3] ^ t0
		A[1] = A[1] ^ t0
		A[4] = A[4] ^ t0
		A[2] = A[2] ^ t0
		A[6] = A[6] ^ t1
		A[9] = A[9] ^ t1
		A[7] = A[7] ^ t1
		A[5] = A[5] ^ t1
		A[8] = A[8] ^ t1
		A[12] = A[12] ^ t2
		A[10] = A[10] ^ t2
		A[13] = A[13] ^ t2
		A[11] = A[11] ^ t2
		A[14] = A[14] ^ t2
		A[18] = A[18] ^ t3
		A[16] = A[16] ^ t3
		A[19] = A[19] ^ t3
		A[17] = A[17] ^ t3
		A[15] = A[15] ^ t3
		A[24] = A[24] ^ t4
		A[22] = A[22] ^ t4
		A[20] = A[20] ^ t4
		A[23] = A[23] ^ t4
		A[21] = A[21] ^ t4
		A[3] = (A[3] << 36) | (A[3] >> (64 - 36))
		A[1] = (A[1] << 3) | (A[1] >> (64 - 3))
		A[4] = (A[4] << 41) | (A[4] >> (64 - 41))
		A[2] = (A[2] << 18) | (A[2] >> (64 - 18))
		A[6] = (A[6] << 1) | (A[6] >> (64 - 1))
		A[9] = (A[9] << 44) | (A[9] >> (64 - 44))
		A[7] = (A[7] << 10) | (A[7] >> (64 - 10))
		A[5] = (A[5] << 45) | (A[5] >> (64 - 45))
		A[8] = (A[8] << 2) | (A[8] >> (64 - 2))
		A[12] = (A[12] << 62) | (A[12] >> (64 - 62))
		A[10] = (A[10] << 6) | (A[10] >> (64 - 6))
		A[13] = (A[13] << 43) | (A[13] >> (64 - 43))
		A[11] = (A[11] << 15) | (A[11] >> (64 - 15))
		A[14] = (A[14] << 61) | (A[14] >> (64 - 61))
		A[18] = (A[18] << 28) | (A[18] >> (64 - 28))
		A[16] = (A[16] << 55) | (A[16] >> (64 - 55))
		A[19] = (A[19] << 25) | (A[19] >> (64 - 25))
		A[17] = (A[17] << 21) | (A[17] >> (64 - 21))
		A[15] = (A[15] << 56) | (A[15] >> (64 - 56))
		A[24] = (A[24] << 27) | (A[24] >> (64 - 27))
		A[22] = (A[22] << 20) | (A[22] >> (64 - 20))
		A[20] = (A[20] << 39) | (A[20] >> (64 - 39))
		A[23] = (A[23] << 8) | (A[23] >> (64 - 8))
		A[21] = (A[21] << 14) | (A[21] >> (64 - 14))

		bnn = 0 - A[13] - 1 //~
		kt = A[9] | A[13]
		c0 = A[0] ^ kt
		kt = bnn | A[17]
		c1 = A[9] ^ kt
		kt = A[17] & A[21]
		c2 = A[13] ^ kt
		kt = A[21] | A[0]
		c3 = A[17] ^ kt
		kt = A[0] & A[9]
		c4 = A[21] ^ kt
		A[0] = c0
		A[9] = c1
		A[13] = c2
		A[17] = c3
		A[21] = c4
		bnn = 0 - A[14] - 1 //~
		kt = A[22] | A[1]
		c0 = A[18] ^ kt
		kt = A[1] & A[5]
		c1 = A[22] ^ kt
		kt = A[5] | bnn
		c2 = A[1] ^ kt
		kt = A[14] | A[18]
		c3 = A[5] ^ kt
		kt = A[18] & A[22]
		c4 = A[14] ^ kt
		A[18] = c0
		A[22] = c1
		A[1] = c2
		A[5] = c3
		A[14] = c4
		bnn = 0 - A[23] - 1 //~
		kt = A[10] | A[19]
		c0 = A[6] ^ kt
		kt = A[19] & A[23]
		c1 = A[10] ^ kt
		kt = bnn & A[2]
		c2 = A[19] ^ kt
		kt = A[2] | A[6]
		c3 = bnn ^ kt
		kt = A[6] & A[10]
		c4 = A[2] ^ kt
		A[6] = c0
		A[10] = c1
		A[19] = c2
		A[23] = c3
		A[2] = c4
		bnn = 0 - A[11] - 1 //~
		kt = A[3] & A[7]
		c0 = A[24] ^ kt
		kt = A[7] | A[11]
		c1 = A[3] ^ kt
		kt = bnn | A[15]
		c2 = A[7] ^ kt
		kt = A[15] & A[24]
		c3 = bnn ^ kt
		kt = A[24] | A[3]
		c4 = A[15] ^ kt
		A[24] = c0
		A[3] = c1
		A[7] = c2
		A[11] = c3
		A[15] = c4
		bnn = 0 - A[16] - 1 //~
		kt = bnn & A[20]
		c0 = A[12] ^ kt
		kt = A[20] | A[4]
		c1 = bnn ^ kt
		kt = A[4] & A[8]
		c2 = A[20] ^ kt
		kt = A[8] | A[12]
		c3 = A[4] ^ kt
		kt = A[12] & A[16]
		c4 = A[8] ^ kt
		A[12] = c0
		A[16] = c1
		A[20] = c2
		A[4] = c3
		A[8] = c4
		A[0] = A[0] ^ RC[j+1]
		t = A[5]
		A[5] = A[18]
		A[18] = A[11]
		A[11] = A[10]
		A[10] = A[6]
		A[6] = A[22]
		A[22] = A[20]
		A[20] = A[12]
		A[12] = A[19]
		A[19] = A[15]
		A[15] = A[24]
		A[24] = A[8]
		A[8] = t
		t = A[1]
		A[1] = A[9]
		A[9] = A[14]
		A[14] = A[2]
		A[2] = A[13]
		A[13] = A[23]
		A[23] = A[4]
		A[4] = A[21]
		A[21] = A[16]
		A[16] = A[3]
		A[3] = A[17]
		A[17] = A[7]
		A[7] = t
	}

	/*
	 * Invert some words back to normal representation.
	 */
	//~x = -x - 1
	A[1] = 0 - A[1] - 1
	A[2] = 0 - A[2] - 1
	A[8] = 0 - A[8] - 1
	A[12] = 0 - A[12] - 1
	A[17] = 0 - A[17] - 1
	A[20] = 0 - A[20] - 1
}

var (
	// ErrInvalidDegree is returned when the degree is not a power of 2
	ErrInvalidDegree = errors.New("n is not valid dimension/degree of the cyclotomic ring")
	// ErrInvalidPolysLenght is returned when the lenght of the polynomials is not equal to each other
	ErrInvalidPolysLength = errors.New("lenght of polynomials is not equal")
)

func isValidDegree(n uint16) bool {
	_, ok := ParamSets[n]
	return ok
}

func GetParamSet(n uint16) PublicParameters {
	if !isValidDegree(n) {
		return PublicParameters{}
	}
	return ParamSets[n]
}

func isValidPolysLength(n uint16, f, g, F, G []int16) bool {
	sum := uint16(len(f) + len(g) + len(F) + len(G))
	return sum%(4*n) == 0
}

func fft3D(polynomials [][][]float64) [][][]complex128 {
	fft3D := make([][][]complex128, len(polynomials))
	for i, row := range polynomials {
		fft3D[i] = make([][]complex128, len(row))
		for j, elt := range row {
			fft3D[i][j] = fft.FFT(elt)
		}
	}
	return fft3D
}

// From f, g, F, G, compute the basis B0 of a NTRU lattice
// as well as its Gram matrix and their fft's.
// return B0FFT, TFFT
func basisAndMatrix(f, g, F, G []int16) ([][][]complex128, internal.FFTtree) {
	B0 := [][][]float64{
		{util.Int16ToFloat64(g), fft.Neg(util.Int16ToFloat64(f))},
		{util.Int16ToFloat64(G), fft.Neg(util.Int16ToFloat64(F))},
	}
	G0 := internal.Gram(B0)
	B0FFT := fft3D(B0)
	G0FFT := fft3D(G0)
	TFFT := new(internal.FFTtree)
	TFFT.FfldlFFT(G0FFT)
	return B0FFT, *TFFT
}

// printTree prints a LDL tree in a human-readable format.
// args: a LDL tree
// Format: coefficient or fft
func printTree(tree []any, prefix string) string {
	leaf := "|_____> "
	top := "|_______"
	son1 := "|       "
	son2 := "        "
	width := len(top)
	var output string

	if len(tree) == 3 {
		if prefix == "" {
			output += prefix + fmt.Sprint(tree[0]) + "\n"
		} else {
			output += prefix[:len(prefix)-width] + top + fmt.Sprint(tree[0]) + "\n"
		}
		output += printTree(tree[1].([]any), prefix+son1)
		output += printTree(tree[2].([]any), prefix+son2)
		return output
	} else {
		return (prefix[:len(prefix)-width] + leaf + fmt.Sprint(tree) + "\n")
	}
}

// Normalize leaves of a LDLD tree (from ||b_i||**2 to sigma/||b_i||)
// args: a LDL tree (T), standar deviation (sigma)
// format: coefficient or fft
func normalizeTree(tree [][]complex128, sigma float64) {
	// python definition: normalize_tree(tree[1], sigma)
	fmt.Printf("\nnormalizeTree: sigma = %f, trees = %v", sigma, tree)
	if len(tree) == 3 {
		normalizeTree([][]complex128{tree[1], nil}, sigma)
		normalizeTree([][]complex128{tree[2], nil}, sigma)
	} else {
		tree[0][0] = complex(sigma/math.Sqrt(real(tree[0][0])), 0)
		tree[0][1] = 0
	}
}

type PublicKey struct {
	n uint16
	h []int16
}

func NewPublicKey() *PublicKey {
	return new(PublicKey)
}

func (privKey *PrivateKey) GetPublicKey() *PublicKey {
	pubKey := NewPublicKey()
	pubKey.n = privKey.n
	// a polynomial such that h*f = g mod (Phi,q)
	pubKey.h, _ = ntt.DivZq(privKey.g, privKey.f)

	return pubKey
}

type Falcon struct {
	//ParamSets
	PrivateKey
	B0FFT [][][]complex128
	TFFT  internal.FFTtree
	h     []int16
}

type PrivateKey struct {
	n uint16
	f []int16
	g []int16
	F []int16
	G []int16
}

// NewPrivateKey returns a new private key struct with empty fields.
func NewPrivateKey() *PrivateKey {
	return new(PrivateKey)
}

// GeneratePrivateKey generates a new private key.
func GeneratePrivateKey(n uint16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	privKey := NewPrivateKey()
	privKey.n = n
	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	privKey.f, privKey.g, privKey.F, privKey.G = internal.NtruGen(n)

	return privKey, nil
}

// GetPrivateKey returns a private key from the given polynomials.
func GetPrivateKey(n uint16, f, g, F, G []int16) (*PrivateKey, error) {
	if !isValidDegree(n) {
		return nil, ErrInvalidDegree
	}
	if !isValidPolysLength(n, f, g, F, G) {
		return nil, ErrInvalidPolysLength
	}
	privKey := NewPrivateKey()
	privKey.n = n
	privKey.f = f
	privKey.g = g
	privKey.F = F
	privKey.G = G

	return privKey, nil
}

// NewKeyPair generates a new keypair coresponding to the valid degree n.
func NewKeyPair(n uint16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
	privKey, err = GeneratePrivateKey(n)
	if err != nil {
		return nil, nil, err
	}

	// Compute NTRU polynomials f, g, F, G verifying fG - gF = q mod Phi
	falcon := new(Falcon)
	falcon.PrivateKey = *privKey
	falcon.B0FFT, falcon.TFFT = basisAndMatrix(
		falcon.PrivateKey.f,
		falcon.PrivateKey.g,
		falcon.PrivateKey.F,
		falcon.PrivateKey.G,
	)
	normalizeTree(falcon.TFFT.AllChild(), ParamSets[n].sigma)
	falcon.h, err = ntt.DivZq(falcon.PrivateKey.g, falcon.PrivateKey.f)
	return privKey, pubKey, nil
}

func NewKeyPairFromPrivateKey(n uint16, polys [4][]int16) (privKey *PrivateKey, pubKey *PublicKey, err error) {
	falcon := new(Falcon)
	if !isValidDegree(n) {
		return nil, nil, ErrInvalidDegree
	}
	if !isValidPolysLength(n, polys[0], polys[1], polys[2], polys[3]) {
		return nil, nil, ErrInvalidPolysLength
	}

	falcon.PrivateKey.f = polys[0]
	falcon.PrivateKey.g = polys[1]
	falcon.PrivateKey.F = polys[2]
	falcon.PrivateKey.G = polys[3]

	falcon.B0FFT, falcon.TFFT = basisAndMatrix(
		falcon.PrivateKey.f,
		falcon.PrivateKey.g,
		falcon.PrivateKey.F,
		falcon.PrivateKey.G,
	)
	normalizeTree(falcon.TFFT.AllChild(), ParamSets[n].sigma)
	falcon.h, err = ntt.DivZq(falcon.PrivateKey.g, falcon.PrivateKey.f)
	return privKey, pubKey, nil
}

// Hash a message to a point in Z[x] mod(Phi, q).
// Inspired by the Parse function from NewHope.

func (privKey *PrivateKey) hashToPoint(message []byte, salt []byte) []float64 {
	if util.Q > (1 << 16) {
		panic("Q is too large")
	}

	k := (1 << 16) / util.Q
	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]float64, privKey.n)
	i := 0
	j := 0
	for i < int(privKey.n) {
		//take two bytes, transform into int16
		//couldn't find shake.Read() definition?
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) + int(buf[1])
		// Implicit rejection sampling
		if elt < k*util.Q {
			hashed[i] = float64(elt % util.Q)
			i++
		}
		j++
	}
	return hashed
}

///////////////////////////////////////////////////////////////////////////////////
//hashToPoint but uses type PublicKey as an assiciator
//type converted from []float64 to []int16

/*func (pubKey *PublicKey) hashToPoint(message []byte, salt []byte) []int16 {
	if util.Q > (1 << 16) {
		panic("Q is too large")
	}

	k := (1 << 16) / util.Q
	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]int16, pubKey.n)
	i := 0
	j := 0
	for i < int(pubKey.n) {
		//take two bytes, transform into int16
		//couldn't find shake.Read() definition?
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) + int(buf[1])
		// Implicit rejection sampling
		if elt < k*util.Q {
			hashed[i] = int16(elt % util.Q)
			i++
		}
		j++
	}
	return hashed
}*/

/*func bytesToUint64s(buf []byte) uint64 {
	i := uint64(binary.LittleEndian.Uint64(buf))
	return i
}

func uint64sToBytes(buf uint64) []byte {
	r := make([]byte, 8)
	binary.LittleEndian.PutUint64(r, buf)
	return r
}*/

const (
	maxRate = 136
)

type storageBuf [maxRate]byte

func (b *storageBuf) asBytes() *[maxRate]byte {
	return (*[maxRate]byte)(b)
}

type inner_shake256_context struct {
	A    [25]uint64
	dbuf []uint8 //points into storage

	storage storageBuf //storage max size is 168 in crypto/x/sha3, in C it's 136
	dptr    int
}

// (reference to sha3 library)
func xorInGeneric(d *inner_shake256_context, buf []byte) {
	n := len(buf) / 8

	for i := 0; i < n; i++ {
		a := binary.LittleEndian.Uint64(buf)
		d.A[i] ^= a
		buf = buf[8:]
	}
}

// copyOutGeneric copies uint64s to a byte buffer (reference to sha3 library)
func copyOutGeneric(d *inner_shake256_context, b []byte) {
	for i := 0; len(b) >= 8; i++ {
		binary.LittleEndian.PutUint64(b, d.A[i])
		b = b[8:]
	}
}

func (sc *inner_shake256_context) shake256_init() {
	sc.dptr = 0
	//memset(sc->st.A, 0, sizeof sc->st.A);
	for j := range sc.A {
		sc.A[j] = 0
	}
	sc.dbuf = sc.storage.asBytes()[:0]
}

/*func (sc *inner_shake256_context) shake256_inject(message []uint8, message_len uint64) {
	dptr := sc.dptr

	for message_len > 0 {
		var clen uint64
		var u uint64

		clen = 136 - dptr
		if clen > message_len {
			clen = message_len
		}

		for u = 0; u < clen; u++ {
			sc.dbuf = append(sc.dbuf, message[u])
		}

		// #endif
		dptr += clen
		message_len -= clen
		if dptr == 136 {
			xorInGeneric(sc, sc.dbuf) //equivalent of permute function in sha3 library
			process_block(&sc.A)
			dptr = 0
		}
	}
	sc.dptr = dptr
}*/

// similar to inject function
func (d *inner_shake256_context) permute_inject() {

	xorInGeneric(d, d.dbuf)
	d.dbuf = d.storage.asBytes()[:0]
	process_block(&d.A)
}

func (d *inner_shake256_context) Write(p []byte) {

	if d.dbuf == nil {
		d.dbuf = d.storage.asBytes()[:0]
	}

	for len(p) > 0 {
		if len(d.dbuf) == 0 && len(p) >= maxRate {
			// The fast path; absorb a full "rate" bytes of input and apply the permutation.
			xorInGeneric(d, p[:maxRate])
			fmt.Println("xor pass")
			p = p[maxRate:]
			process_block(&d.A)
		} else {

			// The slow path; buffer the input until we can fill the sponge, and then xor it in.
			todo := maxRate - len(d.dbuf)
			if todo > len(p) {
				todo = len(p)
			}
			d.dbuf = append(d.dbuf, p[:todo]...)
			p = p[todo:]

			// If the sponge is full, apply the permutation.
			if len(d.dbuf) == maxRate {
				d.permute_inject()
			}
		}
	}
}

func (sc *inner_shake256_context) shake256_flip() {
	copyOutGeneric(sc, sc.dbuf)
	fmt.Println(sc.dbuf)
	sc.dbuf[sc.dptr] ^= 0x1F
	sc.dbuf[maxRate-1] ^= 0x80
	sc.dptr = 136
}

func (d *inner_shake256_context) Read(out *[2]byte) {

	dptr := d.dptr
	n := len(out)

	for len(out) > 0 {
		if dptr == 136 {
			process_block(&d.A)
			dptr = 0
		}
		clen := 136 - dptr
		if clen > n {
			clen = n
		}
		n -= clen
		for i := 0; i < clen; i++ {
			out[i] = d.dbuf[i]
		}
		d.dptr += clen
		d.dbuf = d.dbuf[n:]
		//out = out[n:]
	}
	d.dptr = dptr
}

/*func (sc *inner_shake256_context) shake256_extract(buf *[2]uint8, len uint64) {
	dptr := sc.dptr
	var index uint64

	for len > 0 {

		if dptr == 136 {
			process_block(&sc.A)
			dptr = 0
		}

		clen := 136 - dptr
		if clen > len {
			clen = len
		}
		len -= clen
		sc.dbuf = sc.storage.asBytes()[:dptr+clen]
		// #if
		var i uint64
		for i = 0; i < clen; i++ {
			buf[i] = sc.dbuf[dptr+i]
		}

		//memcpy(out, sc->st.dbuf + dptr, clen);
		dptr += clen
		index += clen
	}
	sc.dptr = dptr
}

func (sc *inner_shake256_context) check() {
	for i := 0; i < 200; i++ {
		fmt.Println(sc.dbuf[i])
	}
}*/

func (pubKey *PublicKey) hashToPoint(message []byte, salt []byte) []int16 {

	//falcon_verify start content starts here
	var hd inner_shake256_context

	hd.shake256_init()
	fmt.Println("init clear")
	hd.Write(salt)
	fmt.Println("inject clear")
	hd.Write(message)
	fmt.Println("inject")
	hd.shake256_flip()
	fmt.Println("flip clear")

	if util.Q > (1 << 16) {
		panic("Q is too large")
	}

	k := (1 << 16) / util.Q
	// Create a SHAKE256 object and hash the salt and message
	/*shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)*/

	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]int16, pubKey.n)
	i := 0
	for i < int(pubKey.n) {
		//take two bytes, transform into int16
		var buf [2]uint8
		hd.Read(&buf)
		// Map the bytes to coefficients
		elt := (uint32(buf[0]) << 8) | uint32(buf[1])
		fmt.Println("first ", buf[0])
		fmt.Println("second ", buf[1])

		// Implicit rejection sampling
		if elt < uint32(k*util.Q) {
			hashed[i] = int16(elt % util.Q)
			i++
		}
	}

	return hashed
}

///////////////////////////////////////////////////////////////////////////////

// Sample a short vector s such that s[0] + s[1] * h = point.
/*func (privKey *PrivateKey) samplePreImage(point []float64) [][]int16 {
	PubParam := GetParamSet(privKey.n)
	B0FFT, TFFT := basisAndMatrix(
		privKey.f,
		privKey.g,
		privKey.F,
		privKey.G,
	)
	a, b, c, d := B0FFT[0][0], B0FFT[0][1], B0FFT[1][0], B0FFT[1][1]
	var s [][]int16
	// We compute a vector t_fft such that:
	//     (fft(point), fft(0)) * B0_fft = t_fft
	// Because fft(0) = 0 and the inverse of B has a very specific form,
	// we can do several optimizations.
	pointFFT := fft.FFT(point)
	t0FFT := make([]complex128, privKey.n)
	t1FFT := make([]complex128, privKey.n)
	for i := 0; i < int(privKey.n); i++ {
		t0FFT[i] = (pointFFT[i] * d[i]) / util.Q
		t1FFT[i] = (-pointFFT[i] * b[i]) / util.Q
	}
	tFFT := [][]complex128{t0FFT, t1FFT}

	// We now compute v such that:
	//     v = z * B0 for an integral vector z
	//     v is close to (point, 0)
	zFFT := TFFT.FfSamplingFFT(tFFT, PubParam.sigmin)

	v0FFT := fft.AddFFT(fft.MulFFT(zFFT[0], a), fft.MulFFT(zFFT[1], c))
	v1FFT := fft.AddFFT(fft.MulFFT(zFFT[0], b), fft.MulFFT(zFFT[1], d))
	v0 := fft.RoundFFTtoInt16(v0FFT)
	v1 := fft.RoundFFTtoInt16(v1FFT)

	// The difference s = (point, 0) - v is such that:
	//     s is short
	//     s[0] + s[1] * h = point
	s[0] = util.SubInt16(util.Float64ToInt16(point), v0)
	s[1] = util.NegInt16(v1)
	return s
}*/

/*func (privKey *PrivateKey) Sign(message []byte) []byte {
	PubParam := GetParamSet(privKey.n)
	signature := []byte{byte(0x30 + LOGN[privKey.n])} // header
	var salt [SaltLen]byte
	util.RandomBytes(salt[:])
	hashed := privKey.hashToPoint(message, salt[:])

	// We repeat the signing procedure until we find a signature that is
	// short enough (both the Euclidean norm and the bytelength)
	for {
		var normSign uint32
		s := privKey.samplePreImage(hashed)

		for _, v := range s[0] {
			normSign += uint32(util.SquareInt16(v))
		}
		for _, v := range s[1] {
			normSign += uint32(util.SquareInt16(v))
		}
		if normSign <= PubParam.sigbound {
			encS, err := internal.Compress(s[1], int(PubParam.sigbytelen-HeadLen-SaltLen))
			if err != nil {
				continue
			}
			signature = append(signature, salt[:]...)
			signature = append(signature, encS...)
			return signature
		}
	}
}*/

func (pubKey *PublicKey) Verify(message []byte, signature []byte) bool {
	//checking
	/*fmt.Println("\npubKey as list: ", pubKey.h)*/
	fmt.Println("\nsignature as list: ", signature)

	salt := signature[HeadLen : HeadLen+SaltLen]
	encS := signature[HeadLen+SaltLen:]
	PubParam := GetParamSet(pubKey.n)

	/*fmt.Println("\nsalt: ", salt)
	fmt.Println("\nSaltLen: ", SaltLen)
	fmt.Println("\nHeadLen: ", HeadLen)
	fmt.Println("\nencS: ", encS)*/

	var normSign uint32
	normSign = 0
	//var ng uint32
	//ng = 0

	var s1 []int16
	// ss1 is dummy-array
	ss1, err := internal.Decompress(encS, int(PubParam.sigbytelen-HeadLen-SaltLen), int(pubKey.n))
	//Decompress working fine

	/*fmt.Println("\nsigPart s1: ", ss1)*/

	if err != nil {
		fmt.Println("invalid encoding")
		return false
	}

	for i := 0; i < len(ss1); i++ {
		s1 = append(s1, int16(ss1[i]))
	}

	// compute s0 and normalize its coefficients in (-q/2, q/2]
	hashed := pubKey.hashToPoint(message, salt)
	fmt.Println("\nhashed value: ", hashed)

	s0 := ntt.SubZq(hashed, ntt.MulZq(s1, pubKey.h))
	/*fmt.Println("\ns0 before normalization: ", s0)
	fmt.Println("\nQ: ", util.Q)*/

	for i := 0; i < len(s0); i++ {
		s0[i] = int16((s0[i]+(util.Q>>1))%util.Q - (util.Q >> 1))
		//s0[i] = int16(uint32(s0[i]) + util.Q&-(uint32(s0[i])>>31))
	}

	/*for i := 0; i < len(s0); i++ {
		s0[i] -= int16(util.Q & -((util.Q >> 1) - uint32(s0[i])>>31))
		//s0[i] = int16(uint32(s0[i]) + util.Q&-(uint32(s0[i])>>31))
	}*/

	/*fmt.Println("\ns0: ", s0)*/

	for _, v := range s0 {
		normSign += uint32(v) * uint32(v)
		//ng |= normSign
	}
	//fmt.Println("\ns0 sum: ", normSign)
	for _, v := range s1 {
		normSign += uint32(v) * uint32(v)
		//ng |= normSign
	}

	//normSign |= -(ng >> 31)

	fmt.Println("\nsignature bound: ", PubParam.sigbound)
	fmt.Println("normSign: ", normSign)
	var sss [2]int
	sss[0] = 2
	sss[1] = 99

	if normSign > PubParam.sigbound {
		return false
	}
	return true
}
