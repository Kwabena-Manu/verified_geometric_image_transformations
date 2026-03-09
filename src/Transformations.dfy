// Tranformations.dfy - Geometric Image Transformations Logic and Verification

// Importing core methods for creating and copying images
include "Core.dfy"

module Transformations {
  // brings all public names declared in Core into the current scope
  import opened Core


  method FlipHorizontal(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.height
    ensures dst.width == src.width
    ensures (forall i, j :: 0 <= i < src.height && 0 <= j <src.width
                            ==>
                              dst.data[i, j] == src.data[i, src.width-1-j]
            )
    ensures fresh(dst.ownsThese)
  {
    dst := new Image(src.height, src.width);
    var newData := new int[src.height, src.width]((i, j) => 0);
    var i := 0;

    while i < src.height
      invariant 0 <= i <= src.height
      invariant ValidImage(dst)
      invariant dst.height == src.height
      invariant dst.width == src.width
      invariant newData.Length0 == src.height
      invariant newData.Length1 == src.width
      invariant (forall x , j :: 0 <= x < i && 0 <= j < src.width
                                 ==>
                                   newData[x, j] == src.data[x, src.width - 1 - j])
    {
      var j := 0;
      while j < src.width
        invariant 0 <= j <= src.width
        invariant ValidImage(dst)
        invariant dst.height == src.height
        invariant dst.width == src.width
        invariant newData.Length0 == src.height
        invariant newData.Length1 == src.width
        invariant (forall x , y :: 0 <= x < i && 0 <= y < src.width
                                   ==>
                                     newData[x, y] == src.data[x, src.width - 1 - y])
        invariant (forall z :: 0 <= z < j
                               ==>
                                 newData[i, z] == src.data[i, src.width - 1 - z])
      {
        newData[i, j] := src.data[i, src.width - 1 - j];
        j := j + 1;
      }
      i := i + 1;
    }

    dst.data := newData;
  }

  // TflipV(i,j) = (h−1−i, j)
  method FlipVertical(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.height
    ensures dst.width == src.width
    ensures (forall i, j :: 0 <= i < src.height && 0 <= j < src.width
                            ==>
                              dst.data[i, j] == src.data[src.height - 1-i, j] )
    ensures fresh(dst.ownsThese)
  {
    dst := new Image(src.height, src.width);
    var newData := new int[src.height, src.width]((_ , _)=> 0);

    var i := 0;

    while i < src.height
      invariant 0 <= i <= src.height
      invariant ValidImage(dst)
      invariant dst.height == src.height
      invariant dst.width == src.width
      invariant newData.Length0 == src.height
      invariant newData.Length1 == src.width
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.width
                                ==>
                                  newData[x,j] == src.data[src.height -1 -x, j])
    {
      var j := 0;

      while j < src.width
        invariant 0 <= j  <= src.width
        invariant ValidImage(dst)
        invariant dst.height == src.height
        invariant dst.width == src.width
        invariant newData.Length0 == src.height
        invariant newData.Length1 == src.width
        invariant (forall x, y :: 0 <= x < i && 0 <= y < src.width
                                  ==>
                                    newData[x,y] == src.data[src.height - 1 -x, y] )
        invariant (forall z :: 0 <= z < j ==> newData[i, z] == src.data[src.height - 1 -i, z])
      {
        newData[i, j ] := src.data[src.height - 1 - i, j];

        j := j + 1;
      }
      i := i + 1;
    }
    dst.data := newData;
  }



  // Method to Rotate 90° Clockwise
  // Transformation: Trot90CW(i,j) = (j, h−1−i), Dimensions: (h,w)→(w,h)
  method Rotate90Clockwise(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.width && dst.width == src.height //swapped dimensions
    ensures (forall i , j :: 0 <= i < src.width && 0 <= j < src.height //swapped dimensions in expression
                             ==>
                               dst.data[i, j] == src.data[src.height - 1 - j, i] )
    ensures fresh(dst.ownsThese)
  {

    dst := new Image(src.width, src.height); //swapped dimensions
    var newData := new int[src.width, src.height]((_,_) => 0);

    var i := 0;

    while i < src.width
      invariant 0 <= i <= src.width
      invariant ValidImage(dst)
      invariant newData.Length0 == src.width
      invariant newData.Length1 == src.height
      invariant dst.height == src.width
      invariant dst.width == src.height
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                ==>
                                  newData[x, j] == src.data[src.height - j -1, x] )
    {
      var j := 0;

      while j < src.height
        invariant 0<= j <= src.height
        invariant ValidImage(dst)
        invariant newData.Length0 == src.width
        invariant newData.Length1 == src.height
        invariant dst.height == src.width
        invariant dst.width == src.height
        invariant (forall x, y :: 0 <= x < i && 0 <= y < src.height
                                  ==>
                                    newData[x,y] == src.data[src.height -y - 1, x])
        invariant (forall z :: 0 <= z < j
                               ==>
                                 newData[i, z] == src.data[src.height-z-1, i])
      {
        newData[i, j] := src.data[src.height-j-1, i];
        j := j + 1;
      }

      i := i +  1;
    }

    dst.data := newData;

  }


  method Rotate90CounterClockwise(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.width && dst.width == src.height
    ensures (forall i, j :: 0 <= i < src.width && 0 <= j < src.height
                            ==>
                              dst.data[i, j] == src.data[j, src.width-1-i])
    ensures fresh(dst.ownsThese)
  {
    dst := new Image(src.width, src.height);
    var newData := new int[src.width, src.height] ((_,_)=> 0);

    var i := 0;

    while i < src.width
      invariant 0 <= i <= src.width
      invariant ValidImage(dst)
      invariant dst.height == src.width
      invariant dst.width == src.height
      invariant newData.Length0 == src.width
      invariant newData.Length1 == src.height
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                ==>
                                  newData[x, j] == src.data[j, src.width - 1 - x])
    {
      var j := 0;

      while j < src.height
        invariant 0 <= j <= src.height
        invariant ValidImage(dst)
        invariant dst.height == src.width
        invariant dst.width == src.height
        invariant newData.Length0 == src.width
        invariant newData.Length1 == src.height
        invariant (forall x, y :: 0 <= x < i && 0 <= y < src.height
                                  ==>
                                    newData[x, y] == src.data[y, src.width - 1 - x])
        invariant (forall z :: 0<= z < j ==> newData[i,z] == src.data[z, src.width -1 -i])
      {

        newData[i, j] := src.data[j, src.width - 1 - i];
        j := j + 1;

      }
      i := i + 1;

    }
    dst.data := newData;


  }


  method Rotate180(src:Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.height
    ensures dst.width == src.width
    ensures (forall i, j :: 0 <= i < src.height && 0 <= j < src.width
                            ==>
                              dst.data[i, j] == src.data[src.height -1 - i, src.width -1 - j] )
    ensures fresh(dst.ownsThese)
  {

    dst := new Image(src.height, src.width);
    var newData := new int[src.height, src.width]((_,_)=> 0);

    var i := 0;

    while i < src.height
      invariant 0<= i <= src.height
      invariant ValidImage(dst)
      invariant dst.height == src.height
      invariant dst.width == src.width
      invariant newData.Length0 == src.height
      invariant newData.Length1 == src.width
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.width
                                ==>
                                  newData[x, j] == src.data[src.height - 1 - x , src.width - 1 - j ] )
    {
      var j := 0;
      while j < src.width
        invariant 0<= j <= src.width
        invariant ValidImage(dst)
        invariant dst.height == src.height
        invariant dst.width == src.width
        invariant newData.Length0 == src.height
        invariant newData.Length1 == src.width
        invariant (forall x, j :: 0 <= x < i && 0 <= j < src.width
                                  ==>
                                    newData[x, j] == src.data[src.height - 1 - x , src.width - 1 - j ] )
        invariant (forall z :: 0 <= z < j ==> newData[i, z] == src.data[src.height - 1 - i, src.width - 1 - z ])
      {
        newData[i, j] := src.data[src.height - 1 - i, src.width - 1 - j];
        j := j + 1;
      }
      i := i + 1;
    }
    dst.data := newData;
  }


  method Rotate270(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.width
    ensures dst.width == src.height
    ensures (forall i, j :: 0 <= i < src.width && 0 <= j < src.height
                            ==>
                              dst.data[i, j] == src.data[j, src.width - 1 - i] )
    ensures fresh(dst.ownsThese)
  {
    dst := new Image(src.width, src.height);
    var newData := new int[src.width, src.height]((_,_)=> 0);

    var i := 0;

    while i < src.width
      invariant 0<= i <= src.width
      invariant ValidImage(dst)
      invariant dst.height == src.width
      invariant dst.width == src.height
      invariant newData.Length0 == src.width
      invariant newData.Length1 == src.height
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                ==>
                                  newData[x, j] == src.data[j , src.width - 1 - x ] )
    {
      var j := 0;
      while j < src.height
        invariant 0<= j <= src.height
        invariant ValidImage(dst)
        invariant dst.height == src.width
        invariant dst.width == src.height
        invariant newData.Length0 == src.width
        invariant newData.Length1 == src.height
        invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                  ==>
                                    newData[x, j] == src.data[j, src.width - 1 - x ] )
        invariant (forall z :: 0 <= z < j ==> newData[i, z] == src.data[z, src.width - 1 - i ])
      {
        newData[i, j] := src.data[j, src.width - 1 - i];
        j := j + 1;
      }
      i := i + 1;
    }
    dst.data := newData;
  }

  method Transpose(src: Image) returns (dst: Image)
    requires ValidImage(src)
    ensures ValidImage(dst)
    ensures dst.height == src.width
    ensures dst.width == src.height
    ensures (forall i, j :: 0 <= i < src.width && 0 <= j < src.height
                            ==>
                              dst.data[i, j] == src.data[j, i] )
    ensures fresh(dst.ownsThese)
  {
    dst := new Image(src.width, src.height);
    var newData := new int[src.width, src.height]((_,_)=> 0);

    var i := 0;

    while i < src.width
      invariant 0<= i <= src.width
      invariant ValidImage(dst)
      invariant dst.height == src.width
      invariant dst.width == src.height
      invariant newData.Length0 == src.width
      invariant newData.Length1 == src.height
      invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                ==>
                                  newData[x, j] == src.data[j , x ] )
    {
      var j := 0;
      while j < src.height
        invariant 0<= j <= src.height
        invariant ValidImage(dst)
        invariant dst.height == src.width
        invariant dst.width == src.height
        invariant newData.Length0 == src.width
        invariant newData.Length1 == src.height
        invariant (forall x, j :: 0 <= x < i && 0 <= j < src.height
                                  ==>
                                    newData[x, j] == src.data[j, x ] )
        invariant (forall z :: 0 <= z < j ==> newData[i, z] == src.data[z,  i ])
      {
        newData[i, j] := src.data[j,  i];
        j := j + 1;
      }
      i := i + 1;
    }
    dst.data := newData;
  }

}