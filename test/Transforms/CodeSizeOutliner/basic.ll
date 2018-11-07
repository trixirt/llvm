; RUN: opt < %s -codesizeoutliner -enable-cso -cso-min-benefit=0 -simplifycfg -S | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define void @foo() #0 {
; CHECK-LABEL: @foo
  %1 = call i32 @someFn(i32 0, i32 1, i32 2)
; CHECK: call {{.*}} @cso_0(i32 2)

  %2 = call i32 @someFn(i32 0, i32 1, i32 4)
; CHECK-NEXT: call {{.*}} @cso_0(i32 4)

  %3 = call i32 @someFn(i32 0, i32 1, i32 6)
; CHECK-NEXT: call {{.*}} @cso_0(i32 6)
  ret void
}



; CHECK:define {{.*}} void @cso_0
; CHECK: call i32 @someFn(i32 0, i32 1, i32 %0)


declare i32 @someFn(i32, i32, i32) #1

attributes #0 = { minsize optsize }
attributes #1 = { minsize optsize }

