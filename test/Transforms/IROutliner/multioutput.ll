; RUN: opt < %s -iroutliner -enable-ir-outliner -iro-min-benefit=1 -simplifycfg -S | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @foo() #0 {
entry:
; CHECK-LABEL entry
  %0 = call i32 @someFn(i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 2)
  %1 = add i32 1, %0
  %2 = udiv i32 1, %0
  
  %3 = call i32 @someFn(i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 2)
  %4 = add i32 1, %3
  %5 = mul i32 1, %0

  %6 = call i32 @someFn(i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 2)
  %7 = add i32 1, %6
  %8 = sub i32 1, %0

  %9 = call i32 @someFn(i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 4)
  %10 = add i32 1, %9


  ; CHECK: call {{.*}} @_iro_0(i32 6)
  ; CHECK: add i32
  ; CHECK-NEXT: ret i32
  %11 = call i32 @someFn(i32 0, i32 0, i32 0, i32 0, i32 0, i32 1, i32 6)
  %12 = add i32 1, %11
  %13 = add i32 %11, %12
  ret i32 %13
}


; CHECK:define {{.*}} @_iro_0(i32)
; CHECK: call {{.*}}i32

declare i32 @someFn(i32, i32, i32, i32, i32, i32, i32) #1

attributes #0 = { minsize optsize }
attributes #1 = { minsize optsize }
