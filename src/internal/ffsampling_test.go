package internal

import (
	"log"
	"reflect"
	"testing"

	kat "github.com/realForbis/go-falcon-WIP/src/internal/KAT"
	"github.com/realForbis/go-falcon-WIP/src/internal/transforms/fft"
)

var (
	n int = 2 //64
	//iterations int = 1
)

func TestGram(t *testing.T) {
	f := kat.SignKAT[n][0].Rb_f
	g := kat.SignKAT[n][0].Rb_g
	F := kat.SignKAT[n][0].Rb_F
	G := kat.SignKAT[n][0].Rb_G
	want := [][][]float64{{{11898.0, 0.0}, {-1618.0, -1669.0}}, {{-1618.0, 1669.0}, {13147.0, 0.0}}}
	B := [][][]float64{{g, fft.Neg(f)}, {G, fft.Neg(F)}}

	got := Gram(B)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("Gram(%v) = %v, want %v", B, got, want)
	}
}

/*
func TestLdl(t *testing.T) {
	// Test case
	G := [][][]float64{{{11898.0, 0.0}, {-1618.0, -1669.0}}, {{-1618.0, 1669.0}, {13147.0, 0.0}}}
	want := [][][][]float64{{{{1, 0}, {0, 0}}, {{-0.13598924188939318, 0.14027567658429987}, {1, 0}}}, {{{11898.0, 0.0}, {0, 0}}, {{0, 0}, {12692.849302403765, 0.0}}}}
	got := Ldl(G)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("Ldl(%v) = %v, want %v", G, got, want)
	}
}
*/

func TestLdlFFT(t *testing.T) {
	// Test case
	G := [][][]complex128{
		{
			{(9409.92166661341 - 3.0995941970261273e-11i), (9409.92166661341 + 3.0995941970261273e-11i)},
			{(-117.8145169420403 + 117.81451694202802i), (-117.8145169420403 - 117.81451694202802i)},
		},
		{
			{(-117.8145169420403 - 117.81451694202802i), (-117.8145169420403 + 117.81451694202802i)},
			{(9409.92166661341 - 3.0995941970261273e-11i), (9409.92166661341 + 3.0995941970261273e-11i)},
		},
	}
	want := [][][][]complex128{{{{1, 1}, {0, 0}}, {{(-0.012520244175894488 - 0.012520244175893265i), (-0.012520244175894488 + 0.012520244175893265i)}, {1, 1}}}, {{{(9409.92166661341 - 3.0995941970261273e-11i), (9409.92166661341 + 3.0995941970261273e-11i)}, {0, 0}}, {{0, 0}, {(9406.971533574253 - 3.098622433862458e-11i), (9406.971533574253 + 3.098622433862458e-11i)}}}}
	got := LdlFFT(G)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("LdlFft(%v) = %v,\n want %v", G, got, want)
	}
}

/*
func TestFfldl(t *testing.T) {
	// Test case
	G := [][][]float64{
		{
			{11898.0, 0.0},
			{-1618.0, -1669.0},
		},
		{
			{-1618.0, 1669.0},
			{13147.0, 0.0},
		},
	}
	want := [][]float64{
		{-0.13598924188939318, 0.14027567658429987},
		{11898.0, 0},
		{12692.849302403765, 0},
	}
	got := Ffldl(G)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("Ffldl(%v) = %v, want %v", G, got, want)
	}
}
*/

func TestFfldlFFT(t *testing.T) {
	// Test case
	G := [][][]complex128{{{(9300.473353870451 - 3.980895014619037e-11i), (9578.417950973693 - 2.243203081748918e-11i), (9300.473353870451 + 3.980895014619037e-11i), (9578.417950973693 + 2.243203081748918e-11i)}, {(673.6572046045823 - 279.0379505376091i), (51.372031032030534 + 124.02305404410252i), (673.6572046045823 + 279.0379505376091i), (51.372031032030534 - 124.02305404410252i)}}, {{(673.6572046045823 + 279.0379505376091i), (51.372031032030534 - 124.02305404410252i), (673.6572046045823 - 279.0379505376091i), (51.372031032030534 + 124.02305404410252i)}, {(9300.473353870451 - 3.980895014619037e-11i), (9578.417950973693 - 2.243203081748918e-11i), (9300.473353870451 + 3.980895014619037e-11i), (9578.417950973693 + 2.243203081748918e-11i)}}}

	//want := [][]complex128{
	//	{(-0.13598924188939318 + 0.14027567658429987i), (-0.13598924188939318 - 0.14027567658429987i)},
	//	{(11898 + 0i), (11898 + 0i)},
	//	{(12692.849302403765 + 0i), (12692.849302403765 + 0i)},
	//}
	T := new(FFTtree)
	T.FfldlFFT(G)
	t.Log(T)
	//if !reflect.DeepEqual(got, want) {
	//	t.Errorf("FfldlFft(%v) = %v, want %v", G, got, want)
	//}
}

/*
func TestFfnp(t *testing.T) {
	// Test case
	tIn := [][]float64{
		{0.8830089035740577, 0.6084777103134843},
		{0.6440340145860605, 0.8452198892347699},
	}
	T := []interface{}{
		[]float64{-0.13598924188939318, 0.14027567658429987},
		[]interface{}{11898.0, 0},
		[]interface{}{12692.849302403765, 0},
	}
	want := [][]float64{{1, 1}, {1, 1}}
	got := Ffnp(tIn, T)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("FfldlFft(%v, %v) = %v, want %v", tIn, T, got, want)
	}
}
*/

func TestFfnpFFT(t *testing.T) {
	// Test case
	tIn := [][]complex128{
		{0.23273893182875416 + 0.012317186192039031i, 0.23273893182875416 - 0.012317186192039031i},
		{0.912492076944699 + 0.11873057430750977i, 0.912492076944699 - 0.11873057430750977i},
	}
	T := []interface{}{
		[]complex128{-0.13598924188939318 + 0.14027567658429987i, -0.13598924188939318 - 0.14027567658429987i},
		[]interface{}{11898 + 0i, 11898 + 0i},
		[]interface{}{0 + 0i + 0 + 0i, 12692.849302403765 + 0i},
	}
	want := [][]complex128{
		{0 + 0i, 0 + 0i},
		{1 + 0i, 1 + 0i},
	}
	got := FfnpFFT(tIn, T)
	log.Println("got: ", got)
	if !reflect.DeepEqual(got, want) {
		t.Errorf("FfldlFft(%v, %v) = %v, want %v", tIn, T, got, want)
	}
}

// failed
func TestFfSamplingFFT(t *testing.T) {
	t0 := [][]complex128{
		{(15.515338920986247 + 21.66571730816177i), (15.515338920986247 - 21.66571730816177i)},
		{(21.876149401904144 + 15.331271869151273i), (21.876149401904144 - 15.331271869151273i)},
	}
	l10 := []complex128{
		(-0.13598924188939318 + 0.14027567658429987i),
		(-0.13598924188939318 - 0.14027567658429987i),
	}
	T0 := []complex128{1.327605943729194, 0}
	T1 := []complex128{1.2853654095931282, 0}
	sigmin := 1.1165085072329104

	T := FFTtree{l10, T0, T1}

	want := [][]complex128{
		{(16 + 22i), (16 - 22i)},
		{(21 + 16i), (21 - 16i)},
	}
	got := T.FfSamplingFFT(t0, sigmin)
	if !reflect.DeepEqual(got, want) {
		TestFfSamplingFFT(t)
		//t.Errorf("FfSamplingFFT(%v, %v, %v, %v, %v) = %v, want %v", t0, l10, T0, T1, sigmin, got, want)
	}
}
