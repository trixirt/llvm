; RUN: opt < %s -iroutliner -enable-ir-outliner -simplifycfg -S | FileCheck %s

target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [1 x i8] zeroinitializer, align 1
@a = common local_unnamed_addr global i32 0, align 4

; Function Attrs: minsize nounwind optsize
define i32 @main() local_unnamed_addr #0 {
entry:
; CHECK-LABEL entry
  %0 = load i32, i32* @a, align 4
  %call = tail call i32 (i64, i8*, i32, ...) bitcast (i32 (...)* @fn1 to i32 (i64, i8*, i32, ...)*)(i64 9, i8* getelementptr inbounds ([1 x i8], [1 x i8]* @.str, i64 0, i64 0), i32 %0) #2
; CHECK: call {{.*}} @_iro_0(i64 9)
  %1 = load i32, i32* @a, align 4
  %call1 = tail call i32 (i64, i8*, i32, ...) bitcast (i32 (...)* @fn1 to i32 (i64, i8*, i32, ...)*)(i64 0, i8* getelementptr inbounds ([1 x i8], [1 x i8]* @.str, i64 0, i64 0), i32 %1) #2
; CHECK: call {{.*}} @_iro_0(i64 0)
  %2 = load i32, i32* @a, align 4
  %call2 = tail call i32 (i64, i8*, i32, ...) bitcast (i32 (...)* @fn1 to i32 (i64, i8*, i32, ...)*)(i64 5, i8* getelementptr inbounds ([1 x i8], [1 x i8]* @.str, i64 0, i64 0), i32 %2) #2
; CHECK: call {{.*}} @_iro_0(i64 5)
  ret i32 0
}

; Function Attrs: minsize optsize
declare i32 @fn1(...) local_unnamed_addr #1

; CHECK:define {{.*}} void @_iro
; CHECK: call {{.*}} @fn1

attributes #0 = { minsize nounwind optsize }
attributes #1 = { minsize optsize }
attributes #2 = { minsize nounwind optsize }


