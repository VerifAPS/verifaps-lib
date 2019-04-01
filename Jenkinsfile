pipeline {
  agent any
  stages {
    stage('Build') {
      steps {
        sh './gradlew classes testClasses'
      }
    }
    stage('Test') {
      parallel {
        stage('Test') {
          steps {
            sh './gradlew check'
            junit(testResults: '**/build/**/*TEST*.xml', allowEmptyResults: true, healthScaleFactor: 1)
          }
        }
        stage('Integration Test') {
          steps {
            sh './gradlew :ide:installDist'
            sh 'share/integration-tests.sh'
          }
        }
      }
    }
    stage('Deploy') {
      steps {
        echo 'test'
      }
    }
  }
}