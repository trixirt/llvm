; RUN: opt < %s -iroutliner -enable-ir-outliner -iro-min-benefit=0 -simplifycfg -S | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @foo() #1 {
entry:
; CHECK-LABEL: @foo
  %0 = call i32 @someFn(i32 0, i32 0, i32 1, i32 2)
  %1 = call i32 @someFn(i32 0, i32 0, i32 1, i32 2)
  %2 = call i32 @someFn(i32 0, i32 0, i32 1, i32 2)
  %3 = call i32 @someFn(i32 0, i32 0, i32 1, i32 4)
  %4 = call i32 @someFn(i32 0, i32 0, i32 1, i32 6)

  ; CHECK: %0 = call {{.*}}i32 @_iro_0(i32 2)
  ; CHECK-NEXT: %1 = call {{.*}} @_iro_0(i32 2)
  ; CHECK-NEXT: %2 = call {{.*}} @_iro_0(i32 2)
  ; CHECK-NEXT: %3 = call {{.*}} @_iro_0(i32 4)
  ; CHECK-NEXT: %4 = call {{.*}} @_iro_0(i32 6)
  ; CHECK-NEXT: ret i32 %4
  ret i32 %4
}


; CHECK:define {{.*}} i32 @_iro_0
; CHECK: call {{.*}}i32 %0)
; CHECK: ret i32 %2


declare i32 @someFn(i32, i32, i32, i32) #1

attributes #0 = { minsize optsize }
attributes #1 = { minsize optsize }
