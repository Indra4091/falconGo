package main

//this file test the parts of the falcon, if they're wokring etc.
//context: rng and some secondary test files are not provided. refer to python version

import (
	//"errors"
	"fmt"
	"math"
	"math/rand"

	//"math/big"
	"time"

	//"github.com/realForbis/go-falcon-WIP/src/internal"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/fft"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/ntt"
	"github.com/realForbis/go-falcon-WIP/src/util"
	//"golang.org/x/crypto/chacha20"
	//"golang.org/x/crypto/sha3"
)

func test_fft(n int, iterations int) bool {
	rand.Seed(time.Now().UnixNano())

	for i := 0; i < iterations; i++ {
		var f = []float64{}
		var g = []float64{}
		var h = []float64{}
		var k = []float64{}

		for j := 0; j < n; j++ {
			f = append(f, float64(rand.Intn(7)-3))
			g = append(g, float64(rand.Intn(7)-3))
		}

		h = fft.Mul(f, g)
		k = fft.Div(h, f)

		for j := 0; j < len(k); j++ {
			k[j] = math.Round(k[j])
		}

		for i := range k {
			if k[i] != g[i] {
				fmt.Println("(f*g)/f=", k)
				fmt.Println("g=", g)
				fmt.Println("mismatch")
				return false
			}
		}
	}
	return true
}

func test_ntt(n int, iterations int) bool {
	//Q defined in util
	rand.Seed(time.Now().UnixNano())

	for i := 0; i < iterations; i++ {
		var f = []int16{}
		var g = []int16{}
		var h = []int16{}
		var k = []int16{}
		var div_err error

		for j := 0; j < n; j++ {
			f = append(f, int16(rand.Intn(util.Q-1)))
			g = append(g, int16(rand.Intn(util.Q-1)))
		}

		h = ntt.MulZq(f, g)
		//different error handling, no try catch!
		k, div_err = ntt.DivZq(h, f)
		if div_err != nil {
			fmt.Println("divided by zero")
			continue
		} else {
			fmt.Println(len(k))
			for i := range k {
				if k[i] != g[i] {
					fmt.Println("(f*g)/f=", k)
					fmt.Println("g=", g)
					fmt.Println("mismatch")
					return false
				}
			}
		}
	}
	return true
}

//didn't check yet!!
/*func check_ntrugen(f []int16, g []int16, F []int16, G []int16) bool{
	//check that f * G - g * F = q mod (x ** n + 1)
	if len(f) == len(g) {
		fmt.Println("equal")
	}

	ff := []*big.Int{}
	GG := []*big.Int{}
	FF := []*big.Int{}
	gg := []*big.Int{}

	a := []*big.Int{}
	b := []*big.Int{}
	//c := []*big.Int{}

	for i:=0; i<len(f); i++ {
		ff[i] = big.NewInt(int64(f[i]))
		GG[i] = big.NewInt(int64(G[i]))
		FF[i] = big.NewInt(int64(F[i]))
		gg[i] = big.NewInt(int64(g[i]))
	}

	//a := internal.karamul(ff, GG)
	//b := internal.karamul(gg, FF)
	//error, karamul not defined?

	/*for i:=0; i< len(f); i++ {
		c[i] = a[i] - b[i]
	}

	for i:=0; i<len(f); i++ {
		if i == 0 && c[i] == big.NewInt(int64(util.Q)) {
			continue
		} else if i != 0 && c[i] == big.NewInt(int64(0)) {
			continue
		} else {
			return false
		}
	}//
	return true
}*/

//didn't check yet!!
/*func test_ntrugen(n uint16, iterations int) bool {
	//test ntrugen
	for i:=0; i< iterations; i++ {
		var f = []int16{}
		var g = []int16{}
		var F = []int16{}
		var G = []int16{}

		f, g, F, G = internal.NtruGen(n)
		if check_ntrugen(f, g, F, G) == false {
			return false
		}
	}
	return true
}*/

/*func wrapper_test(my_test func(int, int), name string, n int, iterations int) {
	//my_test is a function name
	//name is a string, name of the algorithm
	//n is the length of the f,g,F,G
	//iteration is iteration lmao

	var rep bool = my_test(n, iterations)
	if rep == true {
		fmt.Println("passed the test")
	}
}*/

func test_signature(n int, iterations int) {
	var f = []float64{}
	var g = []float64{}
	var F = []float64{}
	var G = []float64{}
	f = sign_KAT[n][0]["f"]
	g = sign_KAT[n][0]["g"]
	F = sign_KAT[n][0]["F"]
	G = sign_KAT[n][0]["G"]

	privKey := newPrivKey()
	pubKey := newPubKey()

}

func main() {
	fmt.Println(test_ntt(5, 10))
}
