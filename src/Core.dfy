module Core {


  // ========== Setting up predicates ==========

  predicate ValidImage(img: Image)
    reads img
    reads img.data
  {
    img.height > 0 &&
    img.width > 0 &&
    img.data.Length0 == img.height &&
    img.data.Length1 == img.width &&
    // img.ownsThese == {img, img.data} &&
    (forall i, j :: 0 <= i < img.height && 0 <= j < img.width
                    ==>
                      0 <= img.data[i,j] <= 255)
  }

  // ============================================

  // Creating a class for an Image

  class Image{

    var data: array2<int>
    var height: int
    var width: int

    ghost const ownsThese: set<object>

    constructor(h: int , w: int)
      requires h > 0 && w > 0
      ensures ValidImage(this)
      ensures this.height == h
      ensures this.width == w

      ensures (forall i, j :: 0 <= i < h && 0 <= j < w
                              ==>
                                this.data[i, j] == 0)

      ensures fresh(ownsThese)
    {
      data := new int[h,w] ((i, j) => 0);
      height := h;
      width := w;
      ownsThese := {this, data};
    }


  }



  // Method to create a new image
  method CreateImage(h: int, w: int) returns (img: Image)
    requires h > 0 && w > 0
    ensures ValidImage(img)
    ensures img.height == h && img.width == w
    ensures forall i,j :: 0 <= i < h && 0 <= j < w ==> img.data[i,j] == 0
    ensures fresh(img.ownsThese)
  {
    img := new Image(h, w);
  }


  // Method to copy an image
  method CopyImage(src: Image) returns (dst: Image)
    requires ValidImage(src)
    // No modifies clause needed for newly allocated dst
    ensures ValidImage(dst)
    ensures dst.height == src.height && dst.width == src.width
    ensures (forall i, j :: 0 <= i < src.height && 0 <= j < src.width
                            ==>
                              dst.data[i,j] == src.data[i,j])
  {

    dst := new Image(src.height, src.width);
    var newData := new [src.height, src.width]((i, j) => 0);

    var i := 0;
    while i < src.height
      // Row Loop bound
      invariant 0 <= i <= src.height
      // Dimensions remain unchanged
      invariant dst.height == src.height
      invariant dst.width == src.width
      invariant newData.Length0 == src.height
      invariant newData.Length1 == src.width
      // Make sure Image remains valid throughout the loop
      invariant ValidImage(dst)
      // Make sure all completed rows are correctly copied
      invariant (forall z, j :: 0 <= z < i  && 0 <= j < dst.width
                                ==>
                                  newData[z, j] == src.data[z, j])
    {
      var j := 0;
      while j < src.width
        //   Column loop bound
        invariant 0 <= j <= src.width
        // Dimensions remain unchanged
        invariant dst.height == src.height
        invariant dst.width == src.width
        invariant newData.Length0 == src.height
        invariant newData.Length1 == src.width
        // Make sure image destination image stays valid
        invariant ValidImage(dst)

        // All rows before i are copied correctly
        invariant (forall x, y :: 0 <= x < i && 0 <= y < dst.width
                                  ==>
                                    newData[x,y] == src.data[x,y] )
        // Make sure all completed columns in the current row up to j are correct
        invariant (forall z :: 0 <= z < j
                               ==>
                                 newData[i, z] == src.data[i, z])
      {
        newData[i, j] := src.data[i,j];
        j := j + 1;
      }

      i := i +1;
    }

    dst.data := newData;
  }



  method GetPixel(img: Image, i: int , j: int) returns (pixel: int)
    requires ValidImage(img)
    requires 0 <= i < img.height && 0 <= j < img.width
    ensures pixel == img.data[i,j]
    ensures 0 <=  pixel <= 255
  {
    pixel := img.data[i,j];
  }

  method SetPixel(img: Image, i: int, j: int, value: int)
    requires ValidImage(img)
    requires 0 <= i < img.height && 0 <= j < img.width
    requires 0 <= value <= 255
    modifies img.data
    ensures ValidImage(img)
    ensures img.data[i, j] == value
    ensures (forall x, y :: (x != i || y != j) &&
                            0 <= x < img.height && 0 <= y < img.width
                            ==>
                              img.data[x, y] == old(img.data[x, y])  )
  {
    img.data[i, j] := value;
  }







}