package falcon

import (
	"errors"
	"fmt"
	"math"
	"math/bits"

	"github.com/realForbis/go-falcon-WIP/src/internal"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/ntt"
	"github.com/realForbis/go-falcon-WIP/src/util"

	"golang.org/x/crypto/sha3"
)

// rc stores the round constants for use in the ι step.
var rc = [24]uint64{
	0x0000000000000001,
	0x0000000000008082,
	0x800000000000808A,
	0x8000000080008000,
	0x000000000000808B,
	0x0000000080000001,
	0x8000000080008081,
	0x8000000000008009,
	0x000000000000008A,
	0x0000000000000088,
	0x0000000080008009,
	0x000000008000000A,
	0x000000008000808B,
	0x800000000000008B,
	0x8000000000008089,
	0x8000000000008003,
	0x8000000000008002,
	0x8000000000000080,
	0x000000000000800A,
	0x800000008000000A,
	0x8000000080008081,
	0x8000000000008080,
	0x0000000080000001,
	0x8000000080008008,
}

// keccakF1600 applies the Keccak permutation to a 1600b-wide
// state represented as a slice of 25 uint64s.
func process_block(a *[25]uint64) {
	// Implementation translated from Keccak-inplace.c
	// in the keccak reference code.
	var t, bc0, bc1, bc2, bc3, bc4, d0, d1, d2, d3, d4 uint64

	for i := 0; i < 24; i += 4 {
		// Combines the 5 steps in each round into 2 steps.
		// Unrolls 4 rounds per loop and spreads some steps across rounds.

		// Round 1
		bc0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]
		bc1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]
		bc2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]
		bc3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]
		bc4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]
		d0 = bc4 ^ (bc1<<1 | bc1>>63)
		d1 = bc0 ^ (bc2<<1 | bc2>>63)
		d2 = bc1 ^ (bc3<<1 | bc3>>63)
		d3 = bc2 ^ (bc4<<1 | bc4>>63)
		d4 = bc3 ^ (bc0<<1 | bc0>>63)

		bc0 = a[0] ^ d0
		t = a[6] ^ d1
		bc1 = bits.RotateLeft64(t, 44)
		t = a[12] ^ d2
		bc2 = bits.RotateLeft64(t, 43)
		t = a[18] ^ d3
		bc3 = bits.RotateLeft64(t, 21)
		t = a[24] ^ d4
		bc4 = bits.RotateLeft64(t, 14)
		a[0] = bc0 ^ (bc2 &^ bc1) ^ rc[i]
		a[6] = bc1 ^ (bc3 &^ bc2)
		a[12] = bc2 ^ (bc4 &^ bc3)
		a[18] = bc3 ^ (bc0 &^ bc4)
		a[24] = bc4 ^ (bc1 &^ bc0)

		t = a[10] ^ d0
		bc2 = bits.RotateLeft64(t, 3)
		t = a[16] ^ d1
		bc3 = bits.RotateLeft64(t, 45)
		t = a[22] ^ d2
		bc4 = bits.RotateLeft64(t, 61)
		t = a[3] ^ d3
		bc0 = bits.RotateLeft64(t, 28)
		t = a[9] ^ d4
		bc1 = bits.RotateLeft64(t, 20)
		a[10] = bc0 ^ (bc2 &^ bc1)
		a[16] = bc1 ^ (bc3 &^ bc2)
		a[22] = bc2 ^ (bc4 &^ bc3)
		a[3] = bc3 ^ (bc0 &^ bc4)
		a[9] = bc4 ^ (bc1 &^ bc0)

		t = a[20] ^ d0
		bc4 = bits.RotateLeft64(t, 18)
		t = a[1] ^ d1
		bc0 = bits.RotateLeft64(t, 1)
		t = a[7] ^ d2
		bc1 = bits.RotateLeft64(t, 6)
		t = a[13] ^ d3
		bc2 = bits.RotateLeft64(t, 25)
		t = a[19] ^ d4
		bc3 = bits.RotateLeft64(t, 8)
		a[20] = bc0 ^ (bc2 &^ bc1)
		a[1] = bc1 ^ (bc3 &^ bc2)
		a[7] = bc2 ^ (bc4 &^ bc3)
		a[13] = bc3 ^ (bc0 &^ bc4)
		a[19] = bc4 ^ (bc1 &^ bc0)

		t = a[5] ^ d0
		bc1 = bits.RotateLeft64(t, 36)
		t = a[11] ^ d1
		bc2 = bits.RotateLeft64(t, 10)
		t = a[17] ^ d2
		bc3 = bits.RotateLeft64(t, 15)
		t = a[23] ^ d3
		bc4 = bits.RotateLeft64(t, 56)
		t = a[4] ^ d4
		bc0 = bits.RotateLeft64(t, 27)
		a[5] = bc0 ^ (bc2 &^ bc1)
		a[11] = bc1 ^ (bc3 &^ bc2)
		a[17] = bc2 ^ (bc4 &^ bc3)
		a[23] = bc3 ^ (bc0 &^ bc4)
		a[4] = bc4 ^ (bc1 &^ bc0)

		t = a[15] ^ d0
		bc3 = bits.RotateLeft64(t, 41)
		t = a[21] ^ d1
		bc4 = bits.RotateLeft64(t, 2)
		t = a[2] ^ d2
		bc0 = bits.RotateLeft64(t, 62)
		t = a[8] ^ d3
		bc1 = bits.RotateLeft64(t, 55)
		t = a[14] ^ d4
		bc2 = bits.RotateLeft64(t, 39)
		a[15] = bc0 ^ (bc2 &^ bc1)
		a[21] = bc1 ^ (bc3 &^ bc2)
		a[2] = bc2 ^ (bc4 &^ bc3)
		a[8] = bc3 ^ (bc0 &^ bc4)
		a[14] = bc4 ^ (bc1 &^ bc0)

		// Round 2
		bc0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]
		bc1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]
		bc2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]
		bc3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]
		bc4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]
		d0 = bc4 ^ (bc1<<1 | bc1>>63)
		d1 = bc0 ^ (bc2<<1 | bc2>>63)
		d2 = bc1 ^ (bc3<<1 | bc3>>63)
		d3 = bc2 ^ (bc4<<1 | bc4>>63)
		d4 = bc3 ^ (bc0<<1 | bc0>>63)

		bc0 = a[0] ^ d0
		t = a[16] ^ d1
		bc1 = bits.RotateLeft64(t, 44)
		t = a[7] ^ d2
		bc2 = bits.RotateLeft64(t, 43)
		t = a[23] ^ d3
		bc3 = bits.RotateLeft64(t, 21)
		t = a[14] ^ d4
		bc4 = bits.RotateLeft64(t, 14)
		a[0] = bc0 ^ (bc2 &^ bc1) ^ rc[i+1]
		a[16] = bc1 ^ (bc3 &^ bc2)
		a[7] = bc2 ^ (bc4 &^ bc3)
		a[23] = bc3 ^ (bc0 &^ bc4)
		a[14] = bc4 ^ (bc1 &^ bc0)

		t = a[20] ^ d0
		bc2 = bits.RotateLeft64(t, 3)
		t = a[11] ^ d1
		bc3 = bits.RotateLeft64(t, 45)
		t = a[2] ^ d2
		bc4 = bits.RotateLeft64(t, 61)
		t = a[18] ^ d3
		bc0 = bits.RotateLeft64(t, 28)
		t = a[9] ^ d4
		bc1 = bits.RotateLeft64(t, 20)
		a[20] = bc0 ^ (bc2 &^ bc1)
		a[11] = bc1 ^ (bc3 &^ bc2)
		a[2] = bc2 ^ (bc4 &^ bc3)
		a[18] = bc3 ^ (bc0 &^ bc4)
		a[9] = bc4 ^ (bc1 &^ bc0)

		t = a[15] ^ d0
		bc4 = bits.RotateLeft64(t, 18)
		t = a[6] ^ d1
		bc0 = bits.RotateLeft64(t, 1)
		t = a[22] ^ d2
		bc1 = bits.RotateLeft64(t, 6)
		t = a[13] ^ d3
		bc2 = bits.RotateLeft64(t, 25)
		t = a[4] ^ d4
		bc3 = bits.RotateLeft64(t, 8)
		a[15] = bc0 ^ (bc2 &^ bc1)
		a[6] = bc1 ^ (bc3 &^ bc2)
		a[22] = bc2 ^ (bc4 &^ bc3)
		a[13] = bc3 ^ (bc0 &^ bc4)
		a[4] = bc4 ^ (bc1 &^ bc0)

		t = a[10] ^ d0
		bc1 = bits.RotateLeft64(t, 36)
		t = a[1] ^ d1
		bc2 = bits.RotateLeft64(t, 10)
		t = a[17] ^ d2
		bc3 = bits.RotateLeft64(t, 15)
		t = a[8] ^ d3
		bc4 = bits.RotateLeft64(t, 56)
		t = a[24] ^ d4
		bc0 = bits.RotateLeft64(t, 27)
		a[10] = bc0 ^ (bc2 &^ bc1)
		a[1] = bc1 ^ (bc3 &^ bc2)
		a[17] = bc2 ^ (bc4 &^ bc3)
		a[8] = bc3 ^ (bc0 &^ bc4)
		a[24] = bc4 ^ (bc1 &^ bc0)

		t = a[5] ^ d0
		bc3 = bits.RotateLeft64(t, 41)
		t = a[21] ^ d1
		bc4 = bits.RotateLeft64(t, 2)
		t = a[12] ^ d2
		bc0 = bits.RotateLeft64(t, 62)
		t = a[3] ^ d3
		bc1 = bits.RotateLeft64(t, 55)
		t = a[19] ^ d4
		bc2 = bits.RotateLeft64(t, 39)
		a[5] = bc0 ^ (bc2 &^ bc1)
		a[21] = bc1 ^ (bc3 &^ bc2)
		a[12] = bc2 ^ (bc4 &^ bc3)
		a[3] = bc3 ^ (bc0 &^ bc4)
		a[19] = bc4 ^ (bc1 &^ bc0)

		// Round 3
		bc0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]
		bc1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]
		bc2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]
		bc3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]
		bc4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]
		d0 = bc4 ^ (bc1<<1 | bc1>>63)
		d1 = bc0 ^ (bc2<<1 | bc2>>63)
		d2 = bc1 ^ (bc3<<1 | bc3>>63)
		d3 = bc2 ^ (bc4<<1 | bc4>>63)
		d4 = bc3 ^ (bc0<<1 | bc0>>63)

		bc0 = a[0] ^ d0
		t = a[11] ^ d1
		bc1 = bits.RotateLeft64(t, 44)
		t = a[22] ^ d2
		bc2 = bits.RotateLeft64(t, 43)
		t = a[8] ^ d3
		bc3 = bits.RotateLeft64(t, 21)
		t = a[19] ^ d4
		bc4 = bits.RotateLeft64(t, 14)
		a[0] = bc0 ^ (bc2 &^ bc1) ^ rc[i+2]
		a[11] = bc1 ^ (bc3 &^ bc2)
		a[22] = bc2 ^ (bc4 &^ bc3)
		a[8] = bc3 ^ (bc0 &^ bc4)
		a[19] = bc4 ^ (bc1 &^ bc0)

		t = a[15] ^ d0
		bc2 = bits.RotateLeft64(t, 3)
		t = a[1] ^ d1
		bc3 = bits.RotateLeft64(t, 45)
		t = a[12] ^ d2
		bc4 = bits.RotateLeft64(t, 61)
		t = a[23] ^ d3
		bc0 = bits.RotateLeft64(t, 28)
		t = a[9] ^ d4
		bc1 = bits.RotateLeft64(t, 20)
		a[15] = bc0 ^ (bc2 &^ bc1)
		a[1] = bc1 ^ (bc3 &^ bc2)
		a[12] = bc2 ^ (bc4 &^ bc3)
		a[23] = bc3 ^ (bc0 &^ bc4)
		a[9] = bc4 ^ (bc1 &^ bc0)

		t = a[5] ^ d0
		bc4 = bits.RotateLeft64(t, 18)
		t = a[16] ^ d1
		bc0 = bits.RotateLeft64(t, 1)
		t = a[2] ^ d2
		bc1 = bits.RotateLeft64(t, 6)
		t = a[13] ^ d3
		bc2 = bits.RotateLeft64(t, 25)
		t = a[24] ^ d4
		bc3 = bits.RotateLeft64(t, 8)
		a[5] = bc0 ^ (bc2 &^ bc1)
		a[16] = bc1 ^ (bc3 &^ bc2)
		a[2] = bc2 ^ (bc4 &^ bc3)
		a[13] = bc3 ^ (bc0 &^ bc4)
		a[24] = bc4 ^ (bc1 &^ bc0)

		t = a[20] ^ d0
		bc1 = bits.RotateLeft64(t, 36)
		t = a[6] ^ d1
		bc2 = bits.RotateLeft64(t, 10)
		t = a[17] ^ d2
		bc3 = bits.RotateLeft64(t, 15)
		t = a[3] ^ d3
		bc4 = bits.RotateLeft64(t, 56)
		t = a[14] ^ d4
		bc0 = bits.RotateLeft64(t, 27)
		a[20] = bc0 ^ (bc2 &^ bc1)
		a[6] = bc1 ^ (bc3 &^ bc2)
		a[17] = bc2 ^ (bc4 &^ bc3)
		a[3] = bc3 ^ (bc0 &^ bc4)
		a[14] = bc4 ^ (bc1 &^ bc0)

		t = a[10] ^ d0
		bc3 = bits.RotateLeft64(t, 41)
		t = a[21] ^ d1
		bc4 = bits.RotateLeft64(t, 2)
		t = a[7] ^ d2
		bc0 = bits.RotateLeft64(t, 62)
		t = a[18] ^ d3
		bc1 = bits.RotateLeft64(t, 55)
		t = a[4] ^ d4
		bc2 = bits.RotateLeft64(t, 39)
		a[10] = bc0 ^ (bc2 &^ bc1)
		a[21] = bc1 ^ (bc3 &^ bc2)
		a[7] = bc2 ^ (bc4 &^ bc3)
		a[18] = bc3 ^ (bc0 &^ bc4)
		a[4] = bc4 ^ (bc1 &^ bc0)

		// Round 4
		bc0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20]
		bc1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21]
		bc2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22]
		bc3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23]
		bc4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24]
		d0 = bc4 ^ (bc1<<1 | bc1>>63)
		d1 = bc0 ^ (bc2<<1 | bc2>>63)
		d2 = bc1 ^ (bc3<<1 | bc3>>63)
		d3 = bc2 ^ (bc4<<1 | bc4>>63)
		d4 = bc3 ^ (bc0<<1 | bc0>>63)

		bc0 = a[0] ^ d0
		t = a[1] ^ d1
		bc1 = bits.RotateLeft64(t, 44)
		t = a[2] ^ d2
		bc2 = bits.RotateLeft64(t, 43)
		t = a[3] ^ d3
		bc3 = bits.RotateLeft64(t, 21)
		t = a[4] ^ d4
		bc4 = bits.RotateLeft64(t, 14)
		a[0] = bc0 ^ (bc2 &^ bc1) ^ rc[i+3]
		a[1] = bc1 ^ (bc3 &^ bc2)
		a[2] = bc2 ^ (bc4 &^ bc3)
		a[3] = bc3 ^ (bc0 &^ bc4)
		a[4] = bc4 ^ (bc1 &^ bc0)

		t = a[5] ^ d0
		bc2 = bits.RotateLeft64(t, 3)
		t = a[6] ^ d1
		bc3 = bits.RotateLeft64(t, 45)
		t = a[7] ^ d2
		bc4 = bits.RotateLeft64(t, 61)
		t = a[8] ^ d3
		bc0 = bits.RotateLeft64(t, 28)
		t = a[9] ^ d4
		bc1 = bits.RotateLeft64(t, 20)
		a[5] = bc0 ^ (bc2 &^ bc1)
		a[6] = bc1 ^ (bc3 &^ bc2)
		a[7] = bc2 ^ (bc4 &^ bc3)
		a[8] = bc3 ^ (bc0 &^ bc4)
		a[9] = bc4 ^ (bc1 &^ bc0)

		t = a[10] ^ d0
		bc4 = bits.RotateLeft64(t, 18)
		t = a[11] ^ d1
		bc0 = bits.RotateLeft64(t, 1)
		t = a[12] ^ d2
		bc1 = bits.RotateLeft64(t, 6)
		t = a[13] ^ d3
		bc2 = bits.RotateLeft64(t, 25)
		t = a[14] ^ d4
		bc3 = bits.RotateLeft64(t, 8)
		a[10] = bc0 ^ (bc2 &^ bc1)
		a[11] = bc1 ^ (bc3 &^ bc2)
		a[12] = bc2 ^ (bc4 &^ bc3)
		a[13] = bc3 ^ (bc0 &^ bc4)
		a[14] = bc4 ^ (bc1 &^ bc0)

		t = a[15] ^ d0
		bc1 = bits.RotateLeft64(t, 36)
		t = a[16] ^ d1
		bc2 = bits.RotateLeft64(t, 10)
		t = a[17] ^ d2
		bc3 = bits.RotateLeft64(t, 15)
		t = a[18] ^ d3
		bc4 = bits.RotateLeft64(t, 56)
		t = a[19] ^ d4
		bc0 = bits.RotateLeft64(t, 27)
		a[15] = bc0 ^ (bc2 &^ bc1)
		a[16] = bc1 ^ (bc3 &^ bc2)
		a[17] = bc2 ^ (bc4 &^ bc3)
		a[18] = bc3 ^ (bc0 &^ bc4)
		a[19] = bc4 ^ (bc1 &^ bc0)

		t = a[20] ^ d0
		bc3 = bits.RotateLeft64(t, 41)
		t = a[21] ^ d1
		bc4 = bits.RotateLeft64(t, 2)
		t = a[22] ^ d2
		bc0 = bits.RotateLeft64(t, 62)
		t = a[23] ^ d3
		bc1 = bits.RotateLeft64(t, 55)
		t = a[24] ^ d4
		bc2 = bits.RotateLeft64(t, 39)
		a[20] = bc0 ^ (bc2 &^ bc1)
		a[21] = bc1 ^ (bc3 &^ bc2)
		a[22] = bc2 ^ (bc4 &^ bc3)
		a[23] = bc3 ^ (bc0 &^ bc4)
		a[24] = bc4 ^ (bc1 &^ bc0)
	}
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

func (pubKey *PublicKey) hashToPoint(message []byte, salt []byte) []int16 {

	// Create a SHAKE256 object and hash the salt and message
	shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)
	// Output pseudo-random bytes and map them to coefficients
	hashed := make([]int16, pubKey.n)
	i := 0

	for i < int(pubKey.n) {
		//take two bytes, transform into int16
		//couldn't find shake.Read() definition?
		var buf [2]byte
		shake.Read(buf[:])
		// Map the bytes to coefficients
		elt := (int(buf[0]) << 8) | int(buf[1])
		// Implicit rejection sampling
		if elt < 61445 {
			hashed[i] = int16(elt % util.Q)
			i++
		}

	}
	return hashed
}

/*const (
	maxRate = 136
)

type inner_shake256_context struct {
	A    [25]uint64
	dbuf []uint8 //points into storage
	dptr int     // points at the current position in dbuf
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
	//memset(sc->st.A, 0, sizeof sc->st.A);
	sc.dptr = 0
	for j := range sc.A {
		sc.A[j] = 0
	}
}

func (d *inner_shake256_context) permute_inject() {
	xorInGeneric(d, d.dbuf)
	process_block(&d.A)
	d.dptr = 0
}

func (d *inner_shake256_context) Write(p []byte) {
	dptr := d.dptr

	for len(p) > 0 {
		if len(d.dbuf) == 0 && len(p) >= maxRate {
			// The fast path; absorb a full "rate" bytes of input and apply the permutation.
			xorInGeneric(d, p[:maxRate])
			p = p[maxRate:]
			process_block(&d.A)
			//ignores the byte buff
		} else {
			// The slow path; buffer the input until we can fill the sponge, and then xor it in.
			todo := maxRate - len(d.dbuf)
			if todo > len(p) {
				todo = len(p)
			}
			d.dbuf = append(d.dbuf, p[:todo]...)
			p = p[todo:]
			xorInGeneric(d, d.dbuf[dptr:dptr+todo])
			dptr += todo

			// If the sponge is full, apply the permutation.
			if len(d.dbuf) == maxRate {
				process_block(&d.A)
				d.dptr = 0
			}
		}
	}

	d.dptr = dptr
}

func (sc *inner_shake256_context) shake256_flip() {
	for i := sc.dptr; i < maxRate; i++ {
		sc.dbuf = append(sc.dbuf, 0)
	}
	copyOutGeneric(sc, sc.dbuf)
	//fmt.Println(sc.dbuf)
	sc.dbuf[sc.dptr] ^= 0x1F
	sc.dbuf[maxRate-1] ^= 0x80
	sc.dptr = 136
}

func (d *inner_shake256_context) Read(out *[2]byte) {

	dptr := d.dptr
	n := len(out)

	for n > 0 {
		if dptr == 136 {
			process_block(&d.A)
			copyOutGeneric(d, d.dbuf)
			dptr = 0
		}
		clen := 136 - dptr
		if clen > n {
			clen = n
		}
		n -= clen
		for i := 0; i < clen; i++ {
			out[i] = d.dbuf[dptr+i]
		}
		dptr += clen
		//d.dbuf = d.dbuf[n:]
		//out = out[n:]
	}
	d.dptr = dptr
}

func (pubKey *PublicKey) hashToPoint(message []byte, salt []byte) []int16 {

	//falcon_verify start content starts here
	var hd inner_shake256_context

	hd.shake256_init()
	fmt.Println("init clear")
	hd.Write(salt)
	fmt.Println("inject salt clear")
	hd.Write(message)
	fmt.Println("inject message clear")
	hd.shake256_flip()
	fmt.Println("flip clear")

	// Create a SHAKE256 object and hash the salt and message
	/*shake := sha3.NewShake256()
	shake.Write(salt)
	shake.Write(message)*/

// Output pseudo-random bytes and map them to coefficients
/*hashed := make([]int16, pubKey.n)
	i := 0
	for i < int(pubKey.n) {
		//take two bytes, transform into int16
		var buf [2]uint8
		hd.Read(&buf)
		// Map the bytes to coefficients
		elt := (uint32(buf[0]) << 8) | uint32(buf[1])

		// Implicit rejection sampling
		if elt < uint32(61445) {
			for elt >= 12289 {
				elt -= 12289
			}
			hashed[i] = int16(elt)
			i++
		}
	}

	return hashed
}*/

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

	/*file, err := ioutil.ReadFile("hashedC.txt")

	if err != nil {
		fmt.Println("error opening hash value")
	}*/

	/*fmt.Println("\npubKey as list: ", pubKey.h)*/
	fmt.Println("\nsignature as list: ", signature)

	salt := signature[HeadLen : HeadLen+SaltLen]
	encS := signature[HeadLen+SaltLen:]
	PubParam := GetParamSet(pubKey.n)

	fmt.Println("\nsalt: ", salt)
	fmt.Println("\nSaltLen: ", SaltLen)
	fmt.Println("\nHeadLen: ", HeadLen)
	fmt.Println("\nencS: ", encS)

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
	fmt.Println("\nlength of the hashed value: ", len(hashed))

	/*hashed = []int16{}

	index := 0
	h := strings.Split(string(file), "\n")
	for _, l := range h {
		bb := strings.NewReader(l)
		scanner1 := bufio.NewScanner(bb)
		scanner1.Split(bufio.ScanWords)
		for scanner1.Scan() {
			x, err := strconv.Atoi(scanner1.Text())
			if err != nil {
				fmt.Println("error in hash read")
			}
			hashed = append(hashed, int16(x))
		}
		index++
	}

	fmt.Println("'\nhashed read: ", hashed)*/

	s0 := ntt.SubZq(hashed, ntt.MulZq(s1, pubKey.h))
	fmt.Println("\ns0 before normalization: ", s0)
	//fmt.Println("\nQ: ", util.Q)

	for i := 0; i < len(s0); i++ {
		s0[i] = int16((s0[i]+(util.Q>>1))%util.Q - (util.Q >> 1))
		//s0[i] = int16(uint32(s0[i]) + util.Q&-(uint32(s0[i])>>31))
		//s0[i] -= int16(util.Q & -((util.Q >> 1) - uint32(s0[i])>>31))
	}

	fmt.Println("\ns0: ", s0)

	for _, v := range s0 {
		normSign += uint32(v) * uint32(v)
	}
	//fmt.Println("\ns0 sum: ", normSign)
	for _, v := range s1 {
		normSign += uint32(v) * uint32(v)
	}

	fmt.Println("\nsignature bound: ", PubParam.sigbound)
	fmt.Println("normSign: ", normSign)

	if normSign > PubParam.sigbound {
		return false
	}
	return true
}
