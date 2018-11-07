; RUN: opt < %s -codesizeoutliner -enable-cso -cso-min-benefit=0 -simplifycfg -S | FileCheck %s
; Check to make sure that the outliner doesn’t outline incompatible functions.

define void @target_cpu_1() #0 {
  %1 = call i32 @someFn(i32 0, i32 1, i32 2)
; CHECK: call {{.*}} @cso_0(i32 2)

  %2 = call i32 @someFn(i32 0, i32 1, i32 4)
; CHECK-NEXT: call {{.*}} @cso_0(i32 4)

  %3 = call i32 @someFn(i32 0, i32 1, i32 6)
; CHECK-NEXT: call {{.*}} @cso_0(i32 6)
  ret void
}


define void @target_cpu_2() #1 {
  %1 = call i32 @someFn(i32 0, i32 1, i32 2)
; CHECK: call {{.*}} @cso_1()
  ret void
}

define void @target_cpu_3() #1 {
  %1 = call i32 @someFn(i32 0, i32 1, i32 2)
; CHECK: call {{.*}} @cso_1()

  %2 = call i32 @someFn(i32 0, i32 1, i32 4)
  ret void
}


; CHECK:define {{.*}} void @cso_0(i32) {{.*}} #0
; CHECK: {{.*}} call i32 @someFn(i32 0, i32 1, i32 %0)

; CHECK:define {{.*}} void @cso_1()  {{.*}} #1
; CHECK: {{.*}} call i32 @someFn(i32 0, i32 1, i32 2)


declare i32 @someFn(i32, i32, i32)

attributes #0 = { minsize optsize "target-cpu"="x86-64" }
attributes #1 = { minsize optsize "target-cpu"="corei7" }