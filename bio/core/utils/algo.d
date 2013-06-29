/*
    This file is part of BioD.
    Copyright (C) 2012    Artem Tarasov <lomereiter@gmail.com>

    Permission is hereby granted, free of charge, to any person obtaining a
    copy of this software and associated documentation files (the "Software"),
    to deal in the Software without restriction, including without limitation
    the rights to use, copy, modify, merge, publish, distribute, sublicense,
    and/or sell copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following conditions:
    
    The above copyright notice and this permission notice shall be included in
    all copies or substantial portions of the Software.
    
    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
    FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
    DEALINGS IN THE SOFTWARE.

*/
module bio.core.utils.algo;

import std.range;

/**
  This function is supposed to be used on a small amount of objects,
  typically tags of the same alignment. Therefore it runs in O(N^2)
  but doesn't require any memory allocations.
*/
bool allDistinct(Range)(Range r) {
    uint sz = 0;
    uint eq = 0;
    foreach (e1; r) {
        ++sz;
        foreach (e2; r) {
            if (e1 == e2) {
                eq += 1;
            }
        }
    }
    return sz == eq;
}

private import std.algorithm;
static if (!__traits(compiles, any!"a == 2"([1,2,3]))) {

    import std.functional;

    /// check if all elements satisfy the condition
    bool all(alias F, R)(R r) {
        foreach (e; r) {
            if (!unaryFun!F(e)) {
                return false;
            }
        }
        return true;
    }

    /// check if any element satisfies the condition
    bool any(alias F, R)(R r) {
        foreach (e; r) {
            if (unaryFun!F(e)) {
                return true;
            }
        }
        return false;
    }
}

import std.functional;

auto argmax(alias func, S)(S set) {
    auto best_elem = set.front;
    auto best_value = unaryFun!func(best_elem);

    set.popFront();
    foreach (elem; set) {
        auto value = unaryFun!func(elem);
        if (value > best_value) {
            best_value = value;
            best_elem = elem;
        }
    }

    return best_elem;
}
